/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace
public import TauCeti.Topology.FiberBundle.Separation

import TauCeti.Geometry.Lie.Subgroup.Differential
import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Naturality

/-!
# The reduced space of a cotangent bundle at zero

Let a Lie group `G` act smoothly, freely and properly on a manifold `Q`, and lift the action to
the cotangent bundle `T*Q`, with its moment map `⟨μ(q, p), ξ⟩ = p(ξ_Q(q))`
(`TauCeti.CotangentBundle.momentMap`). The lifted action is free and proper, so zero is a regular
value of `μ` and the Marsden–Weinstein–Meyer theorem gives the reduced space `μ⁻¹(0) / G` with its
reduced symplectic form `ω_red`, the unique form with `π^* ω_red = i^* ω` for the orbit projection
`π` and the inclusion `i : μ⁻¹(0) → T*Q`
(`existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback` in
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`). The group acting on the level is the coadjoint
stabilizer `G_0` of `0`, which contains every element of `G`.

This file proves **cotangent reduction at zero**: the reduced space is the cotangent bundle of
the orbit space,

`T*Q //₀ G ≅ T*(Q ⧸ G)`,

by a diffeomorphism `Φ` sending the orbit of a horizontal covector `p` at `q` to the covector `p'`
at `[q]` with `p = p' ∘ dπ_q` (`TauCeti.CotangentBundle.reductionMap`), and pulling the canonical
symplectic form of `T*(Q ⧸ G)` back to `ω_red`
(`ProperSMul.exists_diffeomorph_cotangentBundle_orbitRelQuotient`). The tautological forms descend
as well: `Φ^* λ` pulls back along `π` to the restriction of the Liouville form of `T*Q`. The
reduced space has dimension `2 (dim Q - dim G)`
(`ProperSMul.finrank_quotientModelSpace_cotangent`).

The reduction map `Ψ : μ⁻¹(0) → T*(Q ⧸ G)` is smooth and onto, its fibres are exactly the
`G`-orbits, and it pulls back the canonical form of `T*(Q ⧸ G)` to the restriction of that of `T*Q`
(`TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent.Basic`). A map with these properties
onto a manifold of the dimension of the reduced space descends to a diffeomorphism from it which
pulls the form back to the reduced form
(`TauCeti.SmoothTwoForm.exists_diffeomorph_comp_eq_and_mpullback_eq`). This is first stated for
any submersion `ρ : Q → B` with the properties of the orbit projection and any manifold carrying a
nondegenerate form that the level descends to
(`TauCeti.CotangentBundle.exists_diffeomorph_comp_eq_reductionMap_comp`), and then applied to the
orbit projection and the reduced space.

The reduced space is the one of `TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace`,
with its atlas determined by a choice `d` of Lie group structure on `G_0` and the dimension `n` of
the level; the orbit space `Q ⧸ G` carries the atlas `ProperSMul.orbitRelQuotientChartedSpace`.

## Main results

* `TauCeti.CotangentBundle.exists_diffeomorph_comp_eq_reductionMap_comp`: the reduction map
  descends to a diffeomorphism onto `T*B` from any manifold the level descends to along the
  `G`-orbits.
* `ProperSMul.exists_diffeomorph_cotangentBundle_orbitRelQuotient`: cotangent reduction at zero.
* `ProperSMul.finrank_quotientModelSpace_cotangent`: the reduced space has dimension
  `2 (dim Q - dim G)`.

## References

* Jerrold Marsden, Gerard Misiołek, Juan-Pablo Ortega, Matthew Perlmutter and Tudor Ratiu,
  *Hamiltonian Reduction by Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, Section 2.2
  (cotangent bundle reduction at zero).
* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  Springer, 1999, Section 12.1.
-/

public section

noncomputable section

open Function Manifold Module TauCeti TauCeti.CotangentBundle
open scoped ContDiff Manifold

namespace TauCeti.CotangentBundle

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

end TauCeti.CotangentBundle

namespace ProperSMul

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {Q : Type*}
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [MulAction G Q]
  [ContMDiffSMul IG I ∞ G Q] [ContMDiffConstSMul I ∞ G Q] [ProperSMul G Q] [IsCancelSMul G Q]
  {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [I.Boundaryless] [IsManifold I ∞ Q] [MulAction G Q]
  [ContMDiffSMul IG I ∞ G Q] [ContMDiffConstSMul I ∞ G Q] [ProperSMul G Q] [IsCancelSMul G Q] in
/-- **The dimension of the reduced space of a cotangent bundle at zero.** For a Lie group `G`
acting on a manifold `Q`, the model space `ℝ^(n - dim G_0)` of the reduced space of `T*Q` at zero,
where `n = 2 dim Q - dim G` is the dimension of the level `μ⁻¹(0)`, has dimension
`2 (dim Q - dim G)`: the coadjoint stabilizer of `0` is all of `G`. -/
theorem finrank_quotientModelSpace_cotangent
    (hn : finrank ℝ (E × (E →L[ℝ] ℝ)) - finrank ℝ (GroupLieAlgebra IG G) = n)
    (d : Lie.EmbeddedLieSubgroupData IG ((Lie.coadjointRepresentation ℝ IG G).stabilizer 0) F) :
    finrank ℝ (QuotientModelSpace F (Fin n → ℝ)) = 2 * (finrank ℝ E - finrank ℝ EG) := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have hF : finrank ℝ F = finrank ℝ EG := by
    rw [d.finrank_eq_finrank_lieSubalgebraOfSubgroup,
      Lie.finrank_lieSubalgebraOfSubgroup_stabilizer_coadjointRepresentation
        BoundarylessManifold.isInteriorPoint,
      (lieAnnihilator_eq_top_iff ℝ (GroupLieAlgebra IG G)).2 fun ξ ↦ lie_zero ξ]
    exact LieSubalgebra.topEquiv.toLinearEquiv.finrank_eq
  -- The Lie algebra `GroupLieAlgebra IG G` is the model space `EG` of `G` by definition.
  have hg : finrank ℝ (GroupLieAlgebra IG G) = finrank ℝ EG := rfl
  rw [finrank_quotientModelSpace, Module.finrank_fin_fun, hF, ← hn, finrank_prod,
    ContinuousLinearMap.dual_finrank_eq, hg]
  omega

/-- **Cotangent reduction at zero.** Let a Lie group `G` act smoothly, freely and properly on a
manifold `Q`. Then the reduced space `μ⁻¹(0) / G` of the cotangent-lifted action on `T*Q`, for the
atlas given by the dimension `n` of the level and a Lie group structure `d` on the coadjoint
stabilizer `G_0`, is diffeomorphic to the cotangent bundle `T*(Q ⧸ G)` of the orbit space by a
diffeomorphism `Φ` which

* sends the orbit of a horizontal covector `p` at `q` to the covector `p'` at `[q]` with
  `p = p' ∘ dπ_q`;
* pulls the canonical symplectic form `ω` of `T*(Q ⧸ G)` back to the reduced symplectic form: the
  form `Φ^* ω` is symplectic and its pullback along the orbit projection `π : μ⁻¹(0) → μ⁻¹(0) / G`
  is the restriction of the canonical symplectic form of `T*Q` to the level, which characterizes
  the reduced form;
* likewise identifies the tautological forms: the pullback of `Φ^* λ` along `π` is the restriction
  of the Liouville form of `T*Q` to the level. -/
theorem exists_diffeomorph_cotangentBundle_orbitRelQuotient
    (hn : finrank ℝ (E × (E →L[ℝ] ℝ)) - finrank ℝ (GroupLieAlgebra IG G) = n)
    (d : Lie.EmbeddedLieSubgroupData IG ((Lie.coadjointRepresentation ℝ IG G).stabilizer 0) F) :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
    haveI : ContinuousSMul G (CotangentBundle I Q) :=
      ContMDiffSMul.continuousSMul (I := IG) (I' := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
    letI h := isEquivariantMomentMap_momentMap (IG := IG) (G := G) (I := I) (M := Q)
    haveI := h.isCancelSMul_levelSubMulAction (c := 0) fun z _ ↦ IsCancelSMul.stabilizer_eq_bot z
    have hreg := h.forall_differential_surjective_of_stabilizer_eq_bot (c := 0)
      isSymplectic_symplecticForm.isNondegenerate fun z _ ↦ IsCancelSMul.stabilizer_eq_bot z
    letI := h.levelSubMulActionChartedSpace 0 hreg hn
    letI := h.orbitRelQuotientChartedSpace 0 hreg hn d
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    letI := orbitRelQuotientChartedSpace IG G I Q
    ∃ Φ : Diffeomorph 𝓘(ℝ, QuotientModelSpace F (Fin n → ℝ))
        (𝓘(ℝ, QuotientModelSpace EG E).prod 𝓘(ℝ, QuotientModelSpace EG E →L[ℝ] ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ IG G).stabilizer 0)
          (h.levelSubMulAction 0))
        (CotangentBundle 𝓘(ℝ, QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q)) ∞,
      (∀ z, Φ (Quotient.mk _ z) = reductionMap I 𝓘(ℝ, QuotientModelSpace EG E)
          (Quotient.mk (MulAction.orbitRel G Q)) (z : CotangentBundle I Q)) ∧
      SmoothTwoForm.IsSymplectic (SmoothForm.mpullback Φ Φ.contMDiff
        (symplecticForm 𝓘(ℝ, QuotientModelSpace EG E) (MulAction.orbitRel.Quotient G Q))) ∧
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff
          (SmoothForm.mpullback Φ Φ.contMDiff (symplecticForm 𝓘(ℝ, QuotientModelSpace EG E)
            (MulAction.orbitRel.Quotient G Q))) =
        SmoothForm.mpullback Subtype.val
          (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff (symplecticForm I Q) ∧
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff
          (SmoothForm.mpullback Φ Φ.contMDiff (liouvilleForm 𝓘(ℝ, QuotientModelSpace EG E)
            (MulAction.orbitRel.Quotient G Q))) =
        SmoothForm.mpullback Subtype.val
          (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff (liouvilleForm I Q) := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
  have : ContinuousSMul G (CotangentBundle I Q) :=
    ContMDiffSMul.continuousSMul (I := IG) (I' := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
  have h := isEquivariantMomentMap_momentMap (IG := IG) (G := G) (I := I) (M := Q)
  have hfree : ∀ z : CotangentBundle I Q, momentMap IG G z = 0 → MulAction.stabilizer G z = ⊥ :=
    fun z _ ↦ IsCancelSMul.stabilizer_eq_bot z
  have := h.isCancelSMul_levelSubMulAction hfree
  have hreg := h.forall_differential_surjective_of_stabilizer_eq_bot
    isSymplectic_symplecticForm.isNondegenerate hfree
  let := h.levelSubMulActionChartedSpace 0 hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let := h.orbitRelQuotientChartedSpace 0 hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  let := orbitRelQuotientChartedSpace IG G I Q
  -- The reduced symplectic form `η` of the Marsden–Weinstein–Meyer theorem.
  refine (h.existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback hreg hn d
    isSymplectic_symplecticForm fun g ↦ mpullback_smul_symplecticForm g).exists.elim
    fun η hη ↦ ?_
  have hfibρ (q q' : Q) : Quotient.mk (MulAction.orbitRel G Q) q = Quotient.mk _ q' ↔
      ∃ g : G, g • q = q' := by
    rw [eq_comm, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  -- Every element of `G` fixes `0`, so the orbits of `G_0` on the level are those of `G`.
  have hpfib (z z' : h.levelSubMulAction 0) :
      Quotient.mk (MulAction.orbitRel ((Lie.coadjointRepresentation ℝ IG G).stabilizer 0)
        (h.levelSubMulAction 0)) z = Quotient.mk _ z' ↔
      ∃ g : G, g • (z : CotangentBundle I Q) = z' := by
    rw [eq_comm, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨fun ⟨k, hk⟩ ↦ ⟨k, congrArg Subtype.val hk⟩,
      fun ⟨g, hg⟩ ↦ ⟨⟨g, Representation.mem_stabilizer.2 (map_zero _)⟩, Subtype.ext hg⟩⟩
  have hdim : finrank ℝ (QuotientModelSpace F (Fin n → ℝ)) =
      finrank ℝ (QuotientModelSpace EG E × (QuotientModelSpace EG E →L[ℝ] ℝ)) := by
    rw [finrank_quotientModelSpace_cotangent hn d, finrank_quotientModelSpace_prod_dual]
  have key := exists_diffeomorph_comp_eq_reductionMap_comp isSubmersion_quotientMk
    Quotient.mk_surjective ker_mfderiv_quotientMk hfibρ
    (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
    (fun z ↦ h.mem_levelSubMulAction.1 z.2) (fun x hx ↦ ⟨⟨x, h.mem_levelSubMulAction.2 hx⟩, rfl⟩)
    (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d) Quotient.mk_surjective hpfib
    hη.1.isNondegenerate hη.2 hdim
  refine key.elim fun Φ hΦ ↦ ⟨Φ, fun z ↦ congrFun hΦ.1 z, ?_, ?_, hΦ.2.2⟩
  · rw [hΦ.2.1]
    exact hη.1
  · exact (congrArg (SmoothForm.mpullback _
      (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff) hΦ.2.1).trans hη.2

end ProperSMul
