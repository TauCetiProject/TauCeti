/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace

import TauCeti.Geometry.Lie.Subgroup.Differential
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent

/-!
# The reduced space of a cotangent bundle at zero

Let a Lie group `G` act smoothly, freely and properly on a manifold `Q`, and lift the action to the
cotangent bundle `T*Q`, with moment map `⟨μ(q, p), ξ⟩ = p(ξ_Q(q))`
(`TauCeti.CotangentBundle.momentMap`). The lifted action is again free and proper
(`TauCeti.CotangentBundle.instIsCancelSMul`, `TauCeti.CotangentBundle.properSMul`), so every value
of `μ` is regular (`TauCeti.CotangentBundle.differential_momentMap_surjective`), and the
Marsden–Weinstein–Meyer theorem makes the reduced space `T*Q //₀ G = μ⁻¹(0) / G` a smooth manifold
with a unique symplectic form `ω_red` such that `π^* ω_red = i^* ω_Q`, for the orbit projection
`π : μ⁻¹(0) → μ⁻¹(0) / G` and the inclusion `i : μ⁻¹(0) → T*Q`
(`IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback`).
Formally the reduced space is the orbit space of the coadjoint stabilizer `G_0` of `0`, which is
all of `G`, acting on the level.

This file proves the model case of cotangent bundle reduction:

`T*Q //₀ G ≅ T*(Q ⧸ G)`.

A covector `p` at `q` lies in `μ⁻¹(0)` exactly when it vanishes on the orbit directions, which are
the vertical tangent vectors of the orbit projection `Q → Q ⧸ G`; it is then the pullback of a
unique covector `p'` at `[q]`, its *reduced covector*
(`TauCeti.CotangentBundle.reductionMap`). The reduced covector of `(q, p)` depends only on its
`G`-orbit, two covectors in `μ⁻¹(0)` with the same reduced covector lie in one orbit, and every
covector on `Q ⧸ G` is a reduced covector. So `(q, p) ↦ (q, p')` descends to a bijection
`Φ : μ⁻¹(0) / G → T*(Q ⧸ G)`. It is smooth, since its composite with `π` is smooth, and it pulls
the Liouville form `λ` and the canonical symplectic form `ω = -dλ` of `T*(Q ⧸ G)` back to the
descents of those of `T*Q`:

`π^* (Φ^* λ_(Q ⧸ G)) = i^* λ_Q`,  `π^* (Φ^* ω_(Q ⧸ G)) = i^* ω_Q`.

By uniqueness `Φ^* ω_(Q ⧸ G)` is the reduced symplectic form; in particular it is nondegenerate, so
`dΦ` is injective. Both sides have dimension `2 (dim Q - dim G)`, so `Φ` is a local diffeomorphism
by the inverse function theorem, and being bijective it is a diffeomorphism
(`ProperSMul.cotangentReductionDiffeomorph`), indeed a symplectomorphism from `(T*Q //₀ G, ω_red)`
to `(T*(Q ⧸ G), ω)`.

## Main results

* `TauCeti.CotangentBundle.differential_momentMap_surjective`: for a free action, `dμ` is surjective
  at every covector.
* `ProperSMul.finrank_quotientModelSpace_eq_two_mul`: the reduced space `μ⁻¹(0) / G` of a nonempty
  manifold has dimension `2 (dim Q - dim G)`.
* `ProperSMul.cotangentReductionDiffeomorph`: the diffeomorphism `T*Q //₀ G ≅ T*(Q ⧸ G)`, sending
  the orbit of a covector in `μ⁻¹(0)` to its reduced covector
  (`ProperSMul.cotangentReductionDiffeomorph_mk`).
* `ProperSMul.mpullback_quotientMk_mpullback_cotangentReductionDiffeomorph_symplecticForm`,
  `ProperSMul.isSymplectic_mpullback_cotangentReductionDiffeomorph_symplecticForm`: it pulls the
  canonical symplectic form of `T*(Q ⧸ G)` back to the reduced symplectic form.
* `ProperSMul.mpullback_quotientMk_mpullback_cotangentReductionDiffeomorph_liouvilleForm`: it pulls
  the Liouville form of `T*(Q ⧸ G)` back to the descent of the Liouville form of `T*Q`.

## References

* Jerrold Marsden, Gerard Misiołek, Juan-Pablo Ortega, Matthew Perlmutter and Tudor Ratiu,
  *Hamiltonian Reduction by Stages*, Lecture Notes in Mathematics 1913, Springer, 2007,
  Section 2.2 (cotangent bundle reduction at zero, `T*Q //₀ G ≅ T*(Q / G)`).
* Ralph Abraham and Jerrold Marsden, *Foundations of Mechanics*, second edition,
  Benjamin/Cummings, 1978, Section 4.3 (reduction of cotangent bundles).
-/

public section

noncomputable section

open Bundle Function Manifold Module
open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {Q : Type*}
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [MulAction G Q]
  [ContMDiffSMul IG I ∞ G Q] [ContMDiffConstSMul I ∞ G Q]

namespace TauCeti.CotangentBundle

/-- **For a free action, every value of the cotangent moment map is regular.** The cotangent lift
of a free action is free, so the differential `dμ_z` of the cotangent moment map is surjective at
every covector `z`. -/
theorem differential_momentMap_surjective [T2Space Q] [IsCancelSMul G Q]
    (z : CotangentBundle I Q) :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    Surjective
      ((isEquivariantMomentMap_momentMap (IG := IG) (G := G) (I := I) (M := Q)).differential z) :=
  haveI : T2Space G := IG.t2Space_of_lieGroup ∞
  isEquivariantMomentMap_momentMap.forall_differential_surjective_of_stabilizer_eq_bot
    isSymplectic_symplecticForm.isNondegenerate (fun z _ ↦ IsCancelSMul.stabilizer_eq_bot z) z rfl

end TauCeti.CotangentBundle

namespace ProperSMul

open TauCeti TauCeti.CotangentBundle

variable [ProperSMul G Q] [IsCancelSMul G Q]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (d : Lie.EmbeddedLieSubgroupData IG ((Lie.coadjointRepresentation ℝ IG G).stabilizer 0) F)
  {n : ℕ} (hn : finrank ℝ (E × (E →L[ℝ] ℝ)) - finrank ℝ (GroupLieAlgebra IG G) = n)

/-- The cotangent moment map `μ` as a group-level moment map. -/
local notation "hμ₀" => isEquivariantMomentMap_momentMap (IG := IG) (G := G) (I := I) (M := Q)

/-- The coadjoint stabilizer `G_0` of `0`, which is all of `G`. -/
local notation "G₀" => Representation.stabilizer (Lie.coadjointRepresentation ℝ IG G) 0

/-- The zero level `μ⁻¹(0)`, as a `G_0`-space. -/
local notation "Z₀" => SmoothTwoForm.IsEquivariantMomentMap.levelSubMulAction 0 hμ₀

/-- The reduced space `μ⁻¹(0) / G_0`. -/
local notation "R₀" => MulAction.orbitRel.Quotient G₀ Z₀

/-- The orbit space `Q ⧸ G`. -/
local notation "B₀" => MulAction.orbitRel.Quotient G Q

/-- The model with corners of `Q ⧸ G`. -/
local notation "IB₀" => 𝓘(ℝ, QuotientModelSpace EG E)

/-- Every value of the cotangent moment map is regular. -/
local notation "hreg₀" => fun z _ ↦ differential_momentMap_surjective z

/-- The model with corners of `T*(Q ⧸ G)`. -/
local notation "IT₀" => ModelWithCorners.prod IB₀ 𝓘(ℝ, QuotientModelSpace EG E →L[ℝ] ℝ)

/-- The model with corners of the reduced space. -/
local notation "IR₀" => 𝓘(ℝ, QuotientModelSpace F (Fin n → ℝ))

/-- The orbit projection `μ⁻¹(0) → μ⁻¹(0) / G_0` is a submersion. -/
local notation "hπ₀" =>
  SmoothTwoForm.IsEquivariantMomentMap.isSubmersion_quotientMk_levelSubMulAction hμ₀ (c := 0) hreg₀
    hn d

/-- The inclusion `μ⁻¹(0) → T*Q` is a smooth embedding. -/
local notation "hi₀" =>
  SmoothTwoForm.IsEquivariantMomentMap.isSmoothEmbedding_coe_levelSubMulAction hμ₀ (c := 0) hreg₀ hn

/-! ### The reduction map on the reduced space -/

variable (IG G I Q) in
/-- The reduction map `(q, p) ↦ ([q], p')` on the orbit space of the zero level, where `p'` is the
reduced covector of `p`. -/
private def cotangentReductionMap :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
    letI := orbitRelQuotientChartedSpace IG G I Q
    R₀ → CotangentBundle IB₀ B₀ :=
  haveI : T2Space G := IG.t2Space_of_lieGroup ∞
  haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
  letI := orbitRelQuotientChartedSpace IG G I Q
  Quotient.lift (fun z ↦ reductionMap I IB₀ (Quotient.mk (MulAction.orbitRel G Q)) z.1)
    fun z z' hzz' ↦ by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hzz')
      refine ((reductionMap_eq_reductionMap_iff_quotientMk
        ((hμ₀).mem_levelSubMulAction.1 z'.2) ((hμ₀).mem_levelSubMulAction.1 z.2)).2 ⟨g, ?_⟩).symm
      -- The action of `G_0` on the level is by definition the restriction of the action of `G` on
      -- `T*Q`. `SubMulAction.val_smul` does not apply: it would infer the cotangent lift of the
      -- restricted action of `G_0` on `Q`, a different (though defeq) `SMul` instance.
      rw [← hg]
      rfl

/-! ### The dimension of the reduced space -/

include d hn in
/-- **The dimension of `T*Q //₀ G`.** The model space of the reduced space `μ⁻¹(0) / G`, of
dimension `dim T*Q - dim 𝔤 - dim G`, has dimension `2 (dim Q - dim G)`, like that of `T*(Q ⧸ G)`
(`ProperSMul.finrank_quotientModelSpace_prod_dual`). -/
theorem finrank_quotientModelSpace_eq_two_mul :
    finrank ℝ (QuotientModelSpace F (Fin n → ℝ)) = 2 * (finrank ℝ E - finrank ℝ EG) := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  -- `G_0` is all of `G`, whose Lie algebra `𝔤_0 = {ξ | ⁅ξ, 0⁆ = 0}` is all of `𝔤`.
  have h0 : lieAnnihilator ℝ (GroupLieAlgebra IG G) (0 : Module.Dual ℝ (GroupLieAlgebra IG G)) =
      ⊤ :=
    (lieAnnihilator_eq_top_iff _ _).2 fun _ ↦ lie_zero _
  have hF : finrank ℝ F = finrank ℝ EG := by
    rw [d.finrank_eq_finrank_lieSubalgebraOfSubgroup,
      Lie.finrank_lieSubalgebraOfSubgroup_stabilizer_coadjointRepresentation
        BoundarylessManifold.isInteriorPoint, h0]
    exact LieSubalgebra.topEquiv.toLinearEquiv.finrank_eq
  have hE : finrank ℝ (E × (E →L[ℝ] ℝ)) = 2 * finrank ℝ E := by
    rw [finrank_prod, ContinuousLinearMap.dual_finrank_eq, two_mul]
  -- The Lie algebra `𝔤` is by definition the tangent space of `G` at `1`, which is the model `EG`.
  have hG : finrank ℝ (GroupLieAlgebra IG G) = finrank ℝ EG := rfl
  rw [finrank_quotientModelSpace, finrank_pi, Fintype.card_fin, hF, ← hn, hE, hG]
  omega

/-! ### Smoothness and the pulled back forms -/

include d hn in
/-- The reduction map is smooth on the reduced space, since its composite with the orbit
projection is the reduction map along the smooth inclusion of the level. -/
private theorem contMDiff_cotangentReductionMap :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
    letI := orbitRelQuotientChartedSpace IG G I Q
    haveI := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
    letI := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
    letI := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
    ContMDiff IR₀ IT₀ ∞ (cotangentReductionMap IG G I Q) := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
  let _ := orbitRelQuotientChartedSpace IG G I Q
  have := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
  let _ := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
  let _ := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
  have := (hμ₀).isManifold_levelSubMulAction (c := 0) hreg₀ hn
  -- Composed with the orbit projection, the map is the reduction map along the inclusion.
  refine ((hπ₀).contMDiff_comp_iff
    Quotient.mk_surjective le_rfl).1 ?_
  exact contMDiff_reductionMap_comp isSubmersion_quotientMk
    (hi₀).contMDiff
    (fun z ↦ (momentMap_eq_zero_iff_of_ker_eq (ker_mfderiv_quotientMk _)).1
      ((hμ₀).mem_levelSubMulAction.1 z.2)) le_rfl

include d hn in
/-- The reduction map pulls the canonical symplectic form of `T*(Q ⧸ G)` back to the descent of
the canonical symplectic form of `T*Q`. -/
private theorem mpullback_quotientMk_mpullback_cotangentReductionMap_symplecticForm :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
    letI := orbitRelQuotientChartedSpace IG G I Q
    haveI := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
    letI := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
    letI := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
    haveI := (hμ₀).isManifold_levelSubMulAction (c := 0) hreg₀ hn
    haveI := (hμ₀).isManifold_orbitRelQuotient (c := 0) hreg₀ hn d
    SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G₀ Z₀))
        (hπ₀).contMDiff
        (SmoothForm.mpullback (cotangentReductionMap IG G I Q)
          (contMDiff_cotangentReductionMap d hn)
          (symplecticForm IB₀ B₀)) =
      SmoothForm.mpullback (Subtype.val : Z₀ → CotangentBundle I Q)
        (hi₀).contMDiff (symplecticForm I Q) := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
  let _ := orbitRelQuotientChartedSpace IG G I Q
  have := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
  let _ := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
  let _ := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
  have := (hμ₀).isManifold_levelSubMulAction (c := 0) hreg₀ hn
  have := (hμ₀).isManifold_orbitRelQuotient (c := 0) hreg₀ hn d
  refine (LinearMap.congr_fun (SmoothForm.mpullback_comp _ _
    (hπ₀).contMDiff
    (contMDiff_cotangentReductionMap d hn)) _).symm.trans ?_
  -- Composed with the orbit projection, the map is the reduction map along the inclusion.
  exact mpullback_reductionMap_comp_symplecticForm_quotientMk
    (hi₀).contMDiff
    fun z ↦ (hμ₀).mem_levelSubMulAction.1 z.2

include d hn in
/-- The reduction map pulls the Liouville form of `T*(Q ⧸ G)` back to the descent of the
Liouville form of `T*Q`. -/
private theorem mpullback_quotientMk_mpullback_cotangentReductionMap_liouvilleForm :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
    letI := orbitRelQuotientChartedSpace IG G I Q
    haveI := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
    letI := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
    letI := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
    haveI := (hμ₀).isManifold_levelSubMulAction (c := 0) hreg₀ hn
    haveI := (hμ₀).isManifold_orbitRelQuotient (c := 0) hreg₀ hn d
    SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G₀ Z₀))
        (hπ₀).contMDiff
        (SmoothForm.mpullback (cotangentReductionMap IG G I Q)
          (contMDiff_cotangentReductionMap d hn)
          (liouvilleForm IB₀ B₀)) =
      SmoothForm.mpullback (Subtype.val : Z₀ → CotangentBundle I Q)
        (hi₀).contMDiff (liouvilleForm I Q) := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
  let _ := orbitRelQuotientChartedSpace IG G I Q
  have := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
  let _ := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
  let _ := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
  have := (hμ₀).isManifold_levelSubMulAction (c := 0) hreg₀ hn
  have := (hμ₀).isManifold_orbitRelQuotient (c := 0) hreg₀ hn d
  refine (LinearMap.congr_fun (SmoothForm.mpullback_comp _ _
    (hπ₀).contMDiff
    (contMDiff_cotangentReductionMap d hn)) _).symm.trans ?_
  -- Composed with the orbit projection, the map is the reduction map along the inclusion.
  exact mpullback_reductionMap_comp_liouvilleForm isSubmersion_quotientMk
    (hi₀).contMDiff
    fun z ↦ (momentMap_eq_zero_iff_of_ker_eq (ker_mfderiv_quotientMk _)).1
      ((hμ₀).mem_levelSubMulAction.1 z.2)

include d hn in
/-- The Marsden–Weinstein–Meyer reduced symplectic form of `T*Q //₀ G`. -/
private theorem exists_isSymplectic_mpullback_quotientMk_eq_mpullback :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
    letI := orbitRelQuotientChartedSpace IG G I Q
    haveI := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
    letI := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
    letI := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
    haveI := (hμ₀).isManifold_levelSubMulAction (c := 0) hreg₀ hn
    haveI := (hμ₀).isManifold_orbitRelQuotient (c := 0) hreg₀ hn d
    ∃ η : SmoothTwoForm IR₀ R₀, η.IsSymplectic ∧
      SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G₀ Z₀))
          (hπ₀).contMDiff η =
        SmoothForm.mpullback (Subtype.val : Z₀ → CotangentBundle I Q)
          (hi₀).contMDiff
          (symplecticForm I Q) := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
  let _ := orbitRelQuotientChartedSpace IG G I Q
  have := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
  exact ((hμ₀).existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback (c := 0) hreg₀ hn d
    isSymplectic_symplecticForm fun g ↦ mpullback_smul_symplecticForm g).exists

include d hn in
/-- Two-forms on the reduced space are determined by their pullbacks to the level. -/
private theorem injective_mpullback_quotientMk :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
    letI := orbitRelQuotientChartedSpace IG G I Q
    haveI := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
    letI := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
    letI := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
    haveI := (hμ₀).isManifold_levelSubMulAction (c := 0) hreg₀ hn
    haveI := (hμ₀).isManifold_orbitRelQuotient (c := 0) hreg₀ hn d
    Injective (SmoothForm.mpullback (F := ℝ) (k := 2) (Quotient.mk (MulAction.orbitRel G₀ Z₀))
      (hπ₀).contMDiff) := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
  let _ := orbitRelQuotientChartedSpace IG G I Q
  have := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
  let _ := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
  let _ := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
  have := (hμ₀).isManifold_levelSubMulAction (c := 0) hreg₀ hn
  have := (hμ₀).isManifold_orbitRelQuotient (c := 0) hreg₀ hn d
  have hπ := hπ₀
  exact SmoothForm.mpullback_injective_of_surjective hπ.contMDiff Quotient.mk_surjective
    fun z ↦ hπ.surjective_mfderiv (by simp) z

include d hn in
/-- The reduction map pulls the canonical symplectic form of `T*(Q ⧸ G)` back to the reduced
symplectic form, which is symplectic. -/
private theorem isSymplectic_mpullback_cotangentReductionMap_symplecticForm :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
    letI := orbitRelQuotientChartedSpace IG G I Q
    haveI := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
    letI := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
    letI := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
    haveI := (hμ₀).isManifold_levelSubMulAction (c := 0) hreg₀ hn
    haveI := (hμ₀).isManifold_orbitRelQuotient (c := 0) hreg₀ hn d
    SmoothTwoForm.IsSymplectic (SmoothForm.mpullback (cotangentReductionMap IG G I Q)
      (contMDiff_cotangentReductionMap d hn) (symplecticForm IB₀ B₀)) := by
  have hω :=
    mpullback_quotientMk_mpullback_cotangentReductionMap_symplecticForm (I := I) (Q := Q) d hn
  have hπ := injective_mpullback_quotientMk (I := I) (Q := Q) d hn
  -- The reduced form `η` and the pulled back form have the same pullback to the level.
  exact (exists_isSymplectic_mpullback_quotientMk_eq_mpullback (I := I) (Q := Q) d hn).elim
    fun η hη ↦ hπ (hω.trans hη.2.symm) ▸ hη.1

include d hn in
/-- The reduction map is a local diffeomorphism: it pulls a symplectic form back to a symplectic
form, so its differentials are injective, between spaces of the same dimension. -/
private theorem isLocalDiffeomorph_cotangentReductionMap :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
    letI := orbitRelQuotientChartedSpace IG G I Q
    haveI := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
    letI := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
    letI := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
    IsLocalDiffeomorph IR₀ IT₀ ∞ (cotangentReductionMap IG G I Q) := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
  let _ := orbitRelQuotientChartedSpace IG G I Q
  have := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
  let _ := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
  let _ := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
  have := (hμ₀).isManifold_levelSubMulAction (c := 0) hreg₀ hn
  have := (hμ₀).isManifold_orbitRelQuotient (c := 0) hreg₀ hn d
  refine fun x ↦ isLocalDiffeomorphAt_of_injective_mfderiv
    (contMDiff_cotangentReductionMap d hn).contMDiffOn isOpen_univ trivial
    BoundarylessManifold.isInteriorPoint (by simp) ?_ ?_
  · exact ((SmoothTwoForm.IsNondegenerate.isNondegenerate_mpullback_iff
      (hσ := isSymplectic_symplecticForm.isNondegenerate) (contMDiff_cotangentReductionMap d hn)).1
      (isSymplectic_mpullback_cotangentReductionMap_symplecticForm d hn).isNondegenerate).2 x
  · rw [finrank_quotientModelSpace_eq_two_mul d hn, finrank_quotientModelSpace_prod_dual]

variable (IG G I Q) in
/-- The reduction map is bijective: its fibres are the orbits of the zero level, and every covector
on `Q ⧸ G` is a reduced covector. -/
private theorem bijective_cotangentReductionMap :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
    letI := orbitRelQuotientChartedSpace IG G I Q
    Bijective (cotangentReductionMap IG G I Q) := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
  let _ := orbitRelQuotientChartedSpace IG G I Q
  refine ⟨fun x y hxy ↦ ?_, fun w ↦ ?_⟩
  · induction x using Quotient.inductionOn with | h z => ?_
    induction y using Quotient.inductionOn with | h z' => ?_
    obtain ⟨g, hg⟩ := (reductionMap_eq_reductionMap_iff_quotientMk
      ((hμ₀).mem_levelSubMulAction.1 z.2) ((hμ₀).mem_levelSubMulAction.1 z'.2)).1 hxy
    -- `g` lies in `G_0 = G`, since the coadjoint action fixes `0`.
    have hg0 : g ∈ G₀ := by rw [Representation.mem_stabilizer, map_zero]
    -- As in `cotangentReductionMap`, `⟨g, hg0⟩` acts on the level by definition as `g` on `T*Q`.
    exact (Quotient.sound (MulAction.orbitRel_apply.2
      ⟨⟨g, hg0⟩, Subtype.ext hg⟩)).symm
  · obtain ⟨z, hz, rfl⟩ := exists_momentMap_eq_zero_and_reductionMap_eq_quotientMk w
    exact ⟨Quotient.mk _ ⟨z, (hμ₀).mem_levelSubMulAction.2 hz⟩, rfl⟩

/-! ### Cotangent reduction at zero -/

include d hn in
/-- **Cotangent reduction at zero**, `T*Q //₀ G ≅ T*(Q ⧸ G)`. For a free and proper smooth action of
a Lie group `G` on `Q`, the reduced space `μ⁻¹(0) / G` of the cotangent-lifted action, with the
Marsden–Weinstein–Meyer manifold structure for the Lie group structure `d` on `G_0 = G`, is
diffeomorphic to the cotangent bundle of the orbit space `Q ⧸ G`. The diffeomorphism sends the
orbit of a covector `p` at `q` with `μ(q, p) = 0` to the covector `p'` at `[q]` with
`p = p' ∘ dπ_q` (`ProperSMul.cotangentReductionDiffeomorph_mk`). It pulls the canonical symplectic
form of `T*(Q ⧸ G)` back to the reduced symplectic form
(`ProperSMul.mpullback_quotientMk_mpullback_cotangentReductionDiffeomorph_symplecticForm`). -/
def cotangentReductionDiffeomorph :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
    letI := orbitRelQuotientChartedSpace IG G I Q
    haveI := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
    letI := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
    letI := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
    R₀ ≃ₘ⟮IR₀, IT₀⟯ CotangentBundle IB₀ B₀ :=
  haveI : T2Space G := IG.t2Space_of_lieGroup ∞
  haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
  letI := orbitRelQuotientChartedSpace IG G I Q
  haveI := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
  letI := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
  letI := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
  (isLocalDiffeomorph_cotangentReductionMap d hn).diffeomorphOfBijective
    (bijective_cotangentReductionMap IG G I Q)

include d hn in
/-- The cotangent reduction diffeomorphism is the reduction map. -/
private theorem coe_cotangentReductionDiffeomorph :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
    letI := orbitRelQuotientChartedSpace IG G I Q
    haveI := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
    letI := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
    letI := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
    ⇑(cotangentReductionDiffeomorph d hn) = cotangentReductionMap IG G I Q := by
  have : T2Space G := IG.t2Space_of_lieGroup ∞
  have : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
  let _ := orbitRelQuotientChartedSpace IG G I Q
  have := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
  let _ := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
  let _ := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
  exact IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _

/-- **The cotangent reduction diffeomorphism sends the orbit of a covector to its reduced
covector.** The orbit of a covector `p` at `q` with `μ(q, p) = 0` goes to the covector `p'` at
`[q]` with `p = p' ∘ dπ_q` (`TauCeti.CotangentBundle.cotangentRel_reductionMap`). -/
@[simp]
theorem cotangentReductionDiffeomorph_mk :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
    letI := orbitRelQuotientChartedSpace IG G I Q
    haveI := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
    letI := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
    letI := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
    ∀ z : Z₀, cotangentReductionDiffeomorph d hn (Quotient.mk _ z) =
      reductionMap I IB₀ (Quotient.mk (MulAction.orbitRel G Q)) z.1 := by
  intro z
  rw [coe_cotangentReductionDiffeomorph]
  rfl

/-- **The cotangent reduction diffeomorphism is a symplectomorphism**: it pulls the canonical
symplectic form `ω` of `T*(Q ⧸ G)` back to the reduced symplectic form, the unique two-form on
`μ⁻¹(0) / G` whose pullback along the orbit projection `π` is the restriction of `ω_Q` to
`μ⁻¹(0)`. -/
theorem mpullback_quotientMk_mpullback_cotangentReductionDiffeomorph_symplecticForm :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
    letI := orbitRelQuotientChartedSpace IG G I Q
    haveI := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
    letI := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
    letI := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
    haveI := (hμ₀).isManifold_levelSubMulAction (c := 0) hreg₀ hn
    haveI := (hμ₀).isManifold_orbitRelQuotient (c := 0) hreg₀ hn d
    SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G₀ Z₀))
        (hπ₀).contMDiff
        (SmoothForm.mpullback (cotangentReductionDiffeomorph d hn : R₀ → CotangentBundle IB₀ B₀)
          (cotangentReductionDiffeomorph d hn).contMDiff (symplecticForm IB₀ B₀)) =
      SmoothForm.mpullback (Subtype.val : Z₀ → CotangentBundle I Q)
        (hi₀).contMDiff (symplecticForm I Q) := by
  convert mpullback_quotientMk_mpullback_cotangentReductionMap_symplecticForm (I := I) (Q := Q) d hn
    using 4
  exact coe_cotangentReductionDiffeomorph (I := I) (Q := Q) d hn

/-- The pullback of the canonical symplectic form of `T*(Q ⧸ G)` along the cotangent reduction
diffeomorphism is symplectic; it is the reduced symplectic form of `T*Q //₀ G`. -/
theorem isSymplectic_mpullback_cotangentReductionDiffeomorph_symplecticForm :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
    letI := orbitRelQuotientChartedSpace IG G I Q
    haveI := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
    letI := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
    letI := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
    haveI := (hμ₀).isManifold_levelSubMulAction (c := 0) hreg₀ hn
    haveI := (hμ₀).isManifold_orbitRelQuotient (c := 0) hreg₀ hn d
    SmoothTwoForm.IsSymplectic (SmoothForm.mpullback
      (cotangentReductionDiffeomorph d hn : R₀ → CotangentBundle IB₀ B₀)
      (cotangentReductionDiffeomorph d hn).contMDiff (symplecticForm IB₀ B₀)) := by
  convert isSymplectic_mpullback_cotangentReductionMap_symplecticForm (I := I) (Q := Q) d hn using 3
  exact coe_cotangentReductionDiffeomorph (I := I) (Q := Q) d hn

/-- **Descent of the Liouville form.** The cotangent reduction diffeomorphism pulls the Liouville
form `λ` of `T*(Q ⧸ G)` back to the descent of the Liouville form of `T*Q`: its pullback along the
orbit projection `π` is the restriction of `λ_Q` to `μ⁻¹(0)`. -/
theorem mpullback_quotientMk_mpullback_cotangentReductionDiffeomorph_liouvilleForm :
    haveI : T2Space G := IG.t2Space_of_lieGroup ∞
    haveI : T2Space Q := t2Space_of_properSMul_of_t1Group (G := G)
    letI := orbitRelQuotientChartedSpace IG G I Q
    haveI := CotangentBundle.properSMul IG (I := I) (M := Q) (G := G)
    letI := (hμ₀).levelSubMulActionChartedSpace 0 hreg₀ hn
    letI := (hμ₀).orbitRelQuotientChartedSpace 0 hreg₀ hn d
    haveI := (hμ₀).isManifold_levelSubMulAction (c := 0) hreg₀ hn
    haveI := (hμ₀).isManifold_orbitRelQuotient (c := 0) hreg₀ hn d
    SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G₀ Z₀))
        (hπ₀).contMDiff
        (SmoothForm.mpullback (cotangentReductionDiffeomorph d hn : R₀ → CotangentBundle IB₀ B₀)
          (cotangentReductionDiffeomorph d hn).contMDiff (liouvilleForm IB₀ B₀)) =
      SmoothForm.mpullback (Subtype.val : Z₀ → CotangentBundle I Q)
        (hi₀).contMDiff (liouvilleForm I Q) := by
  convert mpullback_quotientMk_mpullback_cotangentReductionMap_liouvilleForm (I := I) (Q := Q) d hn
    using 4
  exact coe_cotangentReductionDiffeomorph (I := I) (Q := Q) d hn

end ProperSMul
