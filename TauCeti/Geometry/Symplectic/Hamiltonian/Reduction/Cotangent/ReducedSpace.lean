/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent.Magnetic.ReducedSpace
public import TauCeti.Topology.FiberBundle.Separation

import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Naturality

/-!
# Cotangent bundle reduction at zero

Let a Lie group `G` act smoothly, freely and properly on a manifold `Q`. The cotangent-lifted
action of `G` on `T*Q` is again free and proper, with coadjoint-equivariant moment map
`⟨μ(q, p), ξ⟩ = p(ξ_Q(q))` (`TauCeti.CotangentBundle.momentMap`). This file proves that the
Marsden–Weinstein–Meyer reduced space of `T*Q` at zero is the cotangent bundle of the orbit space,

`T*Q //₀ G = μ⁻¹(0) / G_0 ≅ T*(Q ⧸ G)`,

by a diffeomorphism carrying the reduced symplectic form to the canonical symplectic form of
`T*(Q ⧸ G)` (`TauCeti.CotangentBundle.zeroReducedSpaceDiffeomorph`). Here `G_0`, the coadjoint
stabilizer of `0 ∈ 𝔤*`, is all of `G`.

* **Regularity.** An element of `G` fixing a covector fixes its base point, so the lifted action is
  free (`TauCeti.CotangentBundle.instIsCancelSMul`), hence so is the action of the coadjoint
  stabilizer of any value on its level, and every value of `μ` is a regular value
  (`TauCeti.CotangentBundle.differential_momentMap_surjective`). The lifted action is proper since
  the bundle projection is equivariant (`TauCeti.CotangentBundle.properSMul`). So the
  Marsden–Weinstein–Meyer theorem (`existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback`
  in `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`) makes `μ⁻¹(0) / G_0` a symplectic manifold.
* **The map.** A covector `p` at `q` lies in `μ⁻¹(0)` exactly when it is the pullback
  `p' ∘ dπ_q` of a covector `p'` at `[q]`, which is then unique. The reduction map
  `(q, p) ↦ ([q], p')` (`TauCeti.CotangentBundle.reductionMap`) is the magnetic reduction map of
  the one-form `α = 0` (`TauCeti.CotangentBundle.magneticReductionMap_zero`).
* **A special case of magnetic reduction.** So cotangent reduction at zero is the case `α = 0`,
  `ν = 0` of magnetic cotangent reduction at a coadjoint-fixed value
  (`TauCeti.CotangentBundle.magneticReducedSpaceDiffeomorph`), with magnetic term `β = 0`: the
  descended reduction map is a diffeomorphism onto `T*(Q ⧸ G)` pulling the canonical symplectic
  form `ω + π^* 0 = ω` back to the reduced symplectic form
  (`TauCeti.CotangentBundle.mpullback_zeroReducedSpaceDiffeomorph_symplecticForm`), and the
  Liouville form of `T*(Q ⧸ G)` back to the form whose pullback to `μ⁻¹(0)` is the restriction of
  the Liouville form of `T*Q`.

The same argument works for any submersion `ρ : Q → B` with the properties of the orbit projection
and any manifold `R` with a nondegenerate form to which the level descends along the `G`-orbits:
the reduction map then descends to a diffeomorphism `R ≅ T*B` matching the forms
(`TauCeti.CotangentBundle.exists_diffeomorph_comp_eq_reductionMap_comp`, through the recognition
of reduced spaces `TauCeti.SmoothTwoForm.exists_diffeomorph_comp_eq_and_mpullback_eq`).

The reduced space carries the atlas of the Marsden–Weinstein–Meyer theorem, which is built from a
proof `h` that `μ` is an equivariant moment map, a proof `hreg` that `0` is a regular value, the
dimension `n = dim T*Q - dim 𝔤` of the level and an embedded Lie subgroup structure `d` on `G_0`.
The statements take these as arguments, as the Marsden–Weinstein–Meyer theorem does; `h` and
`hreg` hold by `TauCeti.CotangentBundle.isEquivariantMomentMap_momentMap` and
`TauCeti.CotangentBundle.differential_momentMap_surjective`.

## Main definitions

* `TauCeti.CotangentBundle.zeroReducedSpaceDiffeomorph`: the diffeomorphism
  `μ⁻¹(0) / G_0 ≅ T*(Q ⧸ G)` induced by the reduction map.

## Main results

* `TauCeti.CotangentBundle.zeroReducedSpaceDiffeomorph_mk`: the diffeomorphism sends the orbit of
  a covector in `μ⁻¹(0)` to its reduced covector.
* `TauCeti.CotangentBundle.mpullback_zeroReducedSpaceDiffeomorph_symplecticForm`: **cotangent
  reduction at zero**, the diffeomorphism pulls the canonical symplectic form of `T*(Q ⧸ G)` back
  to the reduced symplectic form of `μ⁻¹(0) / G_0`.
* `mpullback_quotientMk_mpullback_zeroReducedSpaceDiffeomorph_liouvilleForm`, in
  `TauCeti.CotangentBundle`: descent of the tautological forms.
* `TauCeti.CotangentBundle.exists_diffeomorph_comp_eq_reductionMap_comp`: the reduction map along
  a submersion `ρ : Q → B` descends to a diffeomorphism onto `T*B` from any manifold the level
  descends to along the `G`-orbits.

## References

* Jerrold Marsden, Gerard Misiołek, Juan-Pablo Ortega, Matthew Perlmutter and Tudor Ratiu,
  *Hamiltonian Reduction by Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, Chapter 2
  (cotangent bundle reduction, in particular at zero).
* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23.
-/

public section

noncomputable section

open Function Manifold Module
open scoped ContDiff Manifold

/-! ### Cotangent reduction at zero along a submersion -/

namespace TauCeti.CotangentBundle

section Submersion

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {Q : Type*}
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [MulAction G Q]
  [ContMDiffSMul IG I ∞ G Q] [ContMDiffConstSMul I ∞ G Q]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B] [IsManifold IB ∞ B]
  {EZ HZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
  {IZ : ModelWithCorners ℝ EZ HZ} [IZ.Boundaryless] {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace HZ Z] [IsManifold IZ ∞ Z]
  {ER HR : Type*} [NormedAddCommGroup ER] [NormedSpace ℝ ER] [FiniteDimensional ℝ ER]
  [TopologicalSpace HR] {IR : ModelWithCorners ℝ ER HR} {R : Type*} [TopologicalSpace R]
  [ChartedSpace HR R] [IsManifold IR ∞ R] [BoundarylessManifold IR R]
  {ρ : Q → B} {i : Z → CotangentBundle I Q} {p : Z → R} {η : SmoothTwoForm IR R}

/-- **Cotangent reduction at zero along a submersion.** Let `ρ : Q → B` be a surjective smooth
submersion whose fibres are the `G`-orbits and whose vertical tangent vectors are the orbit
directions, as the orbit projection of a free proper action. Let `i : Z → T*Q` be a smooth map
onto the zero level `μ⁻¹(0)` of the cotangent moment map, and `p : Z → R` a surjective smooth
submersion onto a manifold of the dimension of `T*B` whose fibres are the preimages of the
`G`-orbits, carrying a nondegenerate form `η` with `p^* η = i^* ω`. Then the reduction map
`Ψ : μ⁻¹(0) → T*B` descends to a diffeomorphism `Φ : R → T*B` with `Φ ∘ p = Ψ ∘ i`,
pulling the canonical symplectic form of `T*B` back to `η` and its Liouville form back to a form
whose pullback along `p` is `i^* λ`. -/
theorem exists_diffeomorph_comp_eq_reductionMap_comp
    (hρ : IsSubmersion I IB ∞ ρ) (hρsurj : Surjective ρ)
    (hker : ∀ q, (mfderiv I IB ρ q).ker =
      (InfinitesimalAction.fundamental IG G I Q).orbitTangent q)
    (hfibρ : ∀ q q', ρ q = ρ q' ↔ ∃ g : G, g • q = q')
    (hi : ContMDiff IZ (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ i) (hi0 : ∀ z, momentMap IG G (i z) = 0)
    (hisurj : ∀ x, momentMap IG G x = 0 → ∃ z, i z = x)
    (hp : IsSubmersion IZ IR ∞ p) (hpsurj : Surjective p)
    (hpfib : ∀ z z', p z = p z' ↔ ∃ g : G, g • i z = i z') (hη : η.IsNondegenerate)
    (hpη : SmoothForm.mpullback p hp.contMDiff η = SmoothForm.mpullback i hi (symplecticForm I Q))
    (hdim : finrank ℝ ER = finrank ℝ (EB × (EB →L[ℝ] ℝ))) :
    ∃ Φ : R ≃ₘ⟮IR, IB.prod 𝓘(ℝ, EB →L[ℝ] ℝ)⟯ CotangentBundle IB B,
      ⇑Φ ∘ p = reductionMap I IB ρ ∘ i ∧
      SmoothForm.mpullback Φ Φ.contMDiff (symplecticForm IB B) = η ∧
      SmoothForm.mpullback p hp.contMDiff
          (SmoothForm.mpullback Φ Φ.contMDiff (liouvilleForm IB B)) =
        SmoothForm.mpullback i hi (liouvilleForm I Q) := by
  have hρd (q : Q) : MDifferentiableAt I IB ρ q := (hρ.contMDiff q).mdifferentiableAt (by simp)
  have hρr := hρ.hasRightInverse_mfderiv (by simp)
  have hhor (z : Z) := (momentMap_eq_zero_iff_of_ker_eq (hker (i z).proj)).1 (hi0 z)
  have hΨ := contMDiff_reductionMap_comp hρ hi hhor le_rfl
  refine (SmoothTwoForm.exists_diffeomorph_comp_eq_and_mpullback_eq hp hpsurj hη hΨ (fun w ↦ ?_)
    (fun z z' ↦ ?_) hdim ((mpullback_reductionMap_comp_symplecticForm hρ hi hhor).trans
      hpη.symm)).imp fun Φ hΦ ↦ ⟨hΦ.1, hΦ.2, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := exists_momentMap_eq_zero_and_reductionMap_eq hker hρsurj hρr w
    obtain ⟨z, rfl⟩ := hisurj x hx
    exact ⟨z, rfl⟩
  · exact (reductionMap_eq_reductionMap_iff hker hfibρ hρd hρr (hi0 z) (hi0 z')).trans
      (hpfib z z').symm
  · rw [SmoothForm.mpullback_mpullback]
    simp only [hΦ.1]
    exact mpullback_reductionMap_comp_liouvilleForm hρ hi hhor

end Submersion

end TauCeti.CotangentBundle

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

/-! ### The reduced space at zero is the cotangent bundle of the orbit space -/

section ReducedSpace

variable [ProperSMul G Q] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {n : ℕ}
  (hreg : ∀ z, momentMap IG G z = 0 → Surjective (h.differential z))
  (hn : finrank ℝ (E × (E →L[ℝ] ℝ)) - finrank ℝ (GroupLieAlgebra IG G) = n)
  (d : Lie.EmbeddedLieSubgroupData IG ((Lie.coadjointRepresentation ℝ IG G).stabilizer 0) F)

variable (h) in
/-- **Cotangent bundle reduction at zero.** For a free and proper smooth action of a Lie group `G`
on `Q`, the reduced space `T*Q //₀ G = μ⁻¹(0) / G_0` of the cotangent bundle at zero, with the
atlas of the Marsden–Weinstein–Meyer theorem, is diffeomorphic to the cotangent bundle
`T*(Q ⧸ G)` of the orbit space. The diffeomorphism sends the orbit of a covector `p` at `q` in
`μ⁻¹(0)` to the unique covector `p'` at `[q]` with `p = p' ∘ dπ_q`
(`TauCeti.CotangentBundle.zeroReducedSpaceDiffeomorph_mk`), and it carries the reduced symplectic
form to the canonical symplectic form of `T*(Q ⧸ G)`
(`TauCeti.CotangentBundle.mpullback_zeroReducedSpaceDiffeomorph_symplecticForm`).

The hypotheses `h` and `hreg` are those of the atlas: they hold by
`TauCeti.CotangentBundle.isEquivariantMomentMap_momentMap` and
`TauCeti.CotangentBundle.differential_momentMap_surjective`. -/
def zeroReducedSpaceDiffeomorph :
    haveI := properSMul (IG := IG) (G := G) (I := I) (M := Q)
    letI := h.orbitRelQuotientChartedSpace 0 hreg hn d
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
    MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ IG G).stabilizer 0)
        (h.levelSubMulAction 0) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)),
        𝓘(ℝ, ProperSMul.QuotientModelSpace EG E).prod
          𝓘(ℝ, ProperSMul.QuotientModelSpace EG E →L[ℝ] ℝ)⟯
      CotangentBundle 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q) :=
  magneticReducedSpaceDiffeomorph h (α := 0) (ν := 0) (fun _ ↦ map_zero _) (fun _ _ ↦ by simp)
    hreg hn d

/-- **The diffeomorphism of cotangent reduction at zero sends the orbit of a covector in `μ⁻¹(0)`
to its reduced covector**: the unique covector `p'` at `[q]` with `p = p' ∘ dπ_q`. -/
@[simp]
theorem zeroReducedSpaceDiffeomorph_mk (z : h.levelSubMulAction 0) :
    haveI := properSMul (IG := IG) (G := G) (I := I) (M := Q)
    letI := h.orbitRelQuotientChartedSpace 0 hreg hn d
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
    zeroReducedSpaceDiffeomorph h hreg hn d (Quotient.mk _ z) =
      reductionMap I 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
        (Quotient.mk (MulAction.orbitRel G Q)) (z : CotangentBundle I Q) := by
  have := properSMul (IG := IG) (G := G) (I := I) (M := Q)
  let := h.orbitRelQuotientChartedSpace 0 hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  rw [zeroReducedSpaceDiffeomorph, magneticReducedSpaceDiffeomorph_mk, magneticReductionMap_zero]

/-- **Cotangent bundle reduction at zero: the symplectic forms.** The diffeomorphism
`μ⁻¹(0) / G_0 ≅ T*(Q ⧸ G)` pulls the canonical symplectic form of `T*(Q ⧸ G)` back to the reduced
symplectic form `η` of the Marsden–Weinstein–Meyer theorem, the form on the reduced space with
`π^* η = i^* ω` for the orbit projection `π` and the inclusion `i` of the zero level into `T*Q`
(`existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback` in
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`).
So the diffeomorphism is a symplectomorphism `(T*Q //₀ G, ω_red) ≅ (T*(Q ⧸ G), ω)`. -/
theorem mpullback_zeroReducedSpaceDiffeomorph_symplecticForm :
    haveI := properSMul (IG := IG) (G := G) (I := I) (M := Q)
    letI := h.levelSubMulActionChartedSpace 0 hreg hn
    letI := h.orbitRelQuotientChartedSpace 0 hreg hn d
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    ∀ η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ IG G).stabilizer 0)
          (h.levelSubMulAction 0)),
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff (symplecticForm I Q) →
        SmoothForm.mpullback (zeroReducedSpaceDiffeomorph h hreg hn d)
            (zeroReducedSpaceDiffeomorph h hreg hn d).contMDiff
            (symplecticForm 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
              (MulAction.orbitRel.Quotient G Q)) = η := by
  have := properSMul (IG := IG) (G := G) (I := I) (M := Q)
  let := h.levelSubMulActionChartedSpace 0 hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let := h.orbitRelQuotientChartedSpace 0 hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  intro η hη
  -- Without a magnetic term, `β = 0`, the twisted form is the canonical symplectic form.
  have := mpullback_magneticReducedSpaceDiffeomorph_twistedSymplecticForm (h := h)
    (hαinv := fun _ ↦ map_zero _) (hα := fun _ _ ↦ by simp) hreg hn d
    (by rw [map_zero, map_zero]) η hη
  rwa [twistedSymplecticForm_zero] at this

/-- **Cotangent bundle reduction at zero: the tautological forms.** Along the orbit projection
`π : μ⁻¹(0) → μ⁻¹(0) / G_0`, the diffeomorphism `μ⁻¹(0) / G_0 ≅ T*(Q ⧸ G)` pulls the Liouville form
of `T*(Q ⧸ G)` back to the restriction of the Liouville form of `T*Q` to the zero level. -/
theorem mpullback_quotientMk_mpullback_zeroReducedSpaceDiffeomorph_liouvilleForm :
    haveI := properSMul (IG := IG) (G := G) (I := I) (M := Q)
    letI := h.levelSubMulActionChartedSpace 0 hreg hn
    letI := h.orbitRelQuotientChartedSpace 0 hreg hn d
    letI := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff
        (SmoothForm.mpullback (zeroReducedSpaceDiffeomorph h hreg hn d)
          (zeroReducedSpaceDiffeomorph h hreg hn d).contMDiff
          (liouvilleForm 𝓘(ℝ, ProperSMul.QuotientModelSpace EG E)
            (MulAction.orbitRel.Quotient G Q))) =
      SmoothForm.mpullback Subtype.val (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
        (liouvilleForm I Q) := by
  have := properSMul (IG := IG) (G := G) (I := I) (M := Q)
  let := h.levelSubMulActionChartedSpace 0 hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let := h.orbitRelQuotientChartedSpace 0 hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  let := ProperSMul.orbitRelQuotientChartedSpace IG G I Q
  refine (SmoothForm.mpullback_mpullback _ _ _ (zeroReducedSpaceDiffeomorph h hreg hn d).contMDiff
    _).trans ?_
  -- The diffeomorphism composed with the orbit projection is the reduction map on the level.
  convert mpullback_reductionMap_comp_liouvilleForm ProperSMul.isSubmersion_quotientMk
    (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
    (fun z ↦ (momentMap_eq_zero_iff_of_ker_eq (ProperSMul.ker_mfderiv_quotientMk _)).1
      (h.mem_levelSubMulAction.1 z.property)) using 3
  exact funext (zeroReducedSpaceDiffeomorph_mk hreg hn d)

end ReducedSpace

end TauCeti.CotangentBundle
