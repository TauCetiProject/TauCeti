/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Prod
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.OrbitFiberProduct.ReducedForm
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace

import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.Submersion.Diffeomorph
import TauCeti.Geometry.Manifold.Submersion.Split

/-!
# The shifting theorem

Let a Lie group `G` act smoothly and properly by symplectomorphisms on a symplectic manifold
`(M, σ)`, with coadjoint-equivariant moment map `μ : M → 𝔤*`, let `c` be a regular value of `μ`
whose coadjoint stabilizer `G_c` acts freely on the level `μ⁻¹(c)`, and let `O = G ⧸ G_c` be the
coadjoint orbit of `c`, with its Kirillov–Kostant–Souriau form `ω_KKS` and orbit map
`ι_O [g] = Ad*_g c`.

The **shifting theorem** says that reducing `M` at `c` is the same as reducing `M × O⁻` at zero,
where `O⁻` is the orbit with the reversed form `-ω_KKS`. This file proves it for the
Marsden–Weinstein–Meyer reduced spaces of
`TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace`.

Unless stated otherwise, the declarations named below are in the namespace
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`.

* The diagonal action of `G` on `M × O` preserves `σ ⊞ (-ω_KKS)`, with the coadjoint-equivariant
  moment map `Ψ(x, o) = μ(x) - ι_O(o)` (`prod_neg_coadjointOrbitForm`). Its zero level is the set
  of pairs with `μ(x) = ι_O(o)` (`mem_levelSubMulAction_prod_neg_coadjointOrbitForm`).
* Zero is a regular value of `Ψ` (`forall_differential_surjective_prod_neg_coadjointOrbitForm`),
  and the coadjoint stabilizer `G_0`, which is all of `G`, acts freely on `Ψ⁻¹(0)`
  (`isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm`):
  if `k` fixes `(x, g G_c)`, then `g⁻¹ k g` lies in `G_c` and fixes the point `g⁻¹ • x` of
  `μ⁻¹(c)`. So the Marsden–Weinstein–Meyer theorem applies to `M × O⁻` at zero.
* The map `Ψ⁻¹(0) → μ⁻¹(c) ⧸ G_c`, `(x, g G_c) ↦ [g⁻¹ • x]`, is a surjective smooth submersion
  whose fibres are the orbits of `G_0`: on points it is the orbit projection of the orbit fibre
  product `W_O`, whose transverse fibre-product atlas agrees with the regular-level atlas of
  `Ψ⁻¹(0)`. It
  therefore descends to a diffeomorphism of reduced spaces

  `Φ : Ψ⁻¹(0) ⧸ G_0 ≃ μ⁻¹(c) ⧸ G_c`, `Φ [(x, g G_c)] = [g⁻¹ • x]`

  (`shiftingReducedSpaceDiffeomorph`), with inverse `[z] ↦ [(z, G_c)]`.
* `Φ` pulls the reduced form of `M` at `c` back to the reduced form of `M × O⁻` at zero
  (`mpullback_shiftingReducedSpaceDiffeomorph`):
  pulled back to `Ψ⁻¹(0)`, the first is `pr_M^* σ - pr_O^* ω_KKS`
  (`mpullback_quotientMk_eq_iff_mpullback_orbitFiberProductProj_eq_sub`),
  which is the restriction of `σ ⊞ (-ω_KKS)`. So `Φ` is a symplectomorphism between the two
  reduced spaces.

All Lie group structures on the stabilizers `G_c` and `G_0` are arbitrary, and the theorem holds
for every value `c`, whether or not it is fixed by the coadjoint action.

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`.

* `prod_neg_coadjointOrbitForm`: `Ψ` is a coadjoint-equivariant moment map on `M × O⁻`.
* `forall_differential_surjective_prod_neg_coadjointOrbitForm`: zero is a regular value of `Ψ`.
* `isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm`: `G_0` acts freely on `Ψ⁻¹(0)`.
* `shiftingReducedSpaceDiffeomorph`, `shiftingReducedSpaceDiffeomorph_mk`,
  `shiftingReducedSpaceDiffeomorph_symm_mk`: the diffeomorphism of reduced spaces.
* `mpullback_shiftingReducedSpaceDiffeomorph`: **the shifting theorem**, it is a symplectomorphism.

## References

* E. Meinrenken, *Symplectic geometry*, lecture notes, University of Toronto, 2000,
  Proposition 8.6 (the shifting trick).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 24.4 (the shifting trick for compact groups).
* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 6.1 (orbit reduction and the shifting theorem).
-/

public section

noncomputable section

open Function Module Manifold
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsEquivariantMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
  Lie.isClosed_stabilizer_coadjointRepresentation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {c : Module.Dual ℝ (GroupLieAlgebra I G)}
  (h : σ.IsEquivariantMomentMap μ)

/-! ### The shifting moment map -/

section Level

include h in
variable (c) in
/-- **The shifting moment map.** For the diagonal action of `G` on `M × O`, where `O = G ⧸ G_c`
is the coadjoint orbit of `c`, the map `Ψ(x, o) = μ(x) - ι_O(o)` is a coadjoint-equivariant moment
map of the product form `σ ⊞ (-ω_KKS)`: the sum of `μ` and of the moment map `-ι_O` of the
reversed Kirillov–Kostant–Souriau form. -/
theorem prod_neg_coadjointOrbitForm :
    (σ.prod (-c.coadjointOrbitForm)).IsEquivariantMomentMap
      fun p : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c ↦
        μ p.1 - (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 := by
  simpa only [sub_eq_add_neg] using h.prod c.isEquivariantMomentMap_coadjointOrbitForm.neg

/-- **The zero level of the shifting moment map** consists of the pairs `(x, o)` of `M × O` with
`μ(x) = ι_O(o)`. -/
theorem mem_levelSubMulAction_prod_neg_coadjointOrbitForm
    {p : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c} :
    p ∈ (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0 ↔
      μ p.1 = (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 := by
  rw [mem_levelSubMulAction, sub_eq_zero]

/-- **Zero is a regular value of the shifting moment map** `Ψ(x, o) = μ(x) - ι_O(o)` when `c` is a
regular value of `μ`. -/
theorem forall_differential_surjective_prod_neg_coadjointOrbitForm
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x)) :
    ∀ p : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c,
      μ p.1 - (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 = 0 →
        Function.Surjective ((h.prod_neg_coadjointOrbitForm c).differential p) := by
  intro p hp
  let b := Module.finBasis ℝ (GroupLieAlgebra I G)
  have hreg₀ := isRegularValue_iff.1 (h.isRegularValue_sub_orbitMap hreg b) p
    (funext fun i ↦ by simp [← LinearMap.sub_apply, hp])
  rw [← (h.prod_neg_coadjointOrbitForm c).isRegularPoint_components_iff b]
  simpa only [LinearMap.sub_apply] using hreg₀

/-- **The coadjoint stabilizer of zero acts freely on the zero level of the shifting moment map**
when `G_c` acts freely on the level `μ⁻¹(c)`. -/
theorem isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm
    [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] :
    IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer 0)
      ((h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) := by
  refine isCancelSMul_iff_eq_one_of_smul_eq.2 fun k p hk ↦ ?_
  have hk' : (k : G) • p.val = p.val := congrArg Subtype.val hk
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective p.val.2
  have hx : (k : G) • p.val.1 = p.val.1 := by rw [← Prod.smul_fst, hk']
  have ho : (k : G) • (g : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) = g := by
    rw [hg, ← Prod.smul_snd, hk']
  have hp : μ (g⁻¹ • p.val.1) = c := by
    rw [h.apply_smul, h.mem_levelSubMulAction_prod_neg_coadjointOrbitForm.1 p.property, ← hg,
      Representation.orbitMap_mk, Representation.inv_self_apply]
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at ho
  -- The element `(k g)⁻¹ g = g⁻¹ k⁻¹ g` of `G_c` fixes the point `g⁻¹ • x` of the level.
  have hfix : (⟨_, ho⟩ : (Lie.coadjointRepresentation ℝ I G).stabilizer c) •
      (⟨g⁻¹ • p.val.1, h.mem_levelSubMulAction.2 hp⟩ : h.levelSubMulAction c) =
      ⟨g⁻¹ • p.val.1, h.mem_levelSubMulAction.2 hp⟩ := by
    refine Subtype.ext ?_
    simp [mul_smul, inv_smul_eq_iff.2 hx.symm]
  refine Subtype.ext ?_
  simpa [mul_assoc, inv_mul_eq_one] using congrArg Subtype.val (IsCancelSMul.eq_one_of_smul hfix)

end Level

/-! ### The reduced space of `M × O⁻` at zero -/

section Reduced

variable [FiniteDimensional ℝ E'] [I'.Boundaryless] [ProperSMul G M]
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
  {n : ℕ} (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)
  {n₀ : ℕ} (hn₀ : finrank ℝ (E' × Subgroup.QuotientModelSpace I
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) - finrank ℝ (GroupLieAlgebra I G) = n₀)
  {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [FiniteDimensional ℝ F₀]
  (d₀ : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer 0) F₀)

/-- The zero level of the shifting moment map and the orbit fibre product, read in the basis
`Module.finBasis`, have the same points. -/
private def levelEquivOrbitFiberProduct :
    (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0 ≃
      OrbitFiberProduct μ c (Module.finBasis ℝ (GroupLieAlgebra I G)) :=
  (Equiv.refl _).subtypeEquiv fun _ ↦ h.mem_levelSubMulAction_prod_neg_coadjointOrbitForm.trans
    (components_eq_orbitMap_iff_apply_eq _).symm

omit [FiniteDimensional ℝ E'] [I'.Boundaryless] [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- The identification of the zero level with the orbit fibre product is the identity of points. -/
private theorem coe_levelEquivOrbitFiberProduct
    (p : (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) :
    ((h.levelEquivOrbitFiberProduct p : OrbitFiberProduct μ c
      (Module.finBasis ℝ (GroupLieAlgebra I G))) :
        M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) = p :=
  (rfl)

/-- The identity of points is a diffeomorphism from the regular-level atlas of the zero level of
the shifting moment map to the transverse fibre-product atlas of the orbit fibre product: both make
the inclusion into `M × O` a smooth embedding. -/
private def levelDiffeomorphOrbitFiberProduct :
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    letI := h.orbitFiberProductChartedSpace c hreg (Module.finBasis ℝ (GroupLieAlgebra I G))
    (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0 ≃ₘ⟮𝓘(ℝ, Fin n₀ → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ (Subgroup.QuotientModelSpace I
        ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (Fin (finrank ℝ (GroupLieAlgebra I G)) → ℝ)) → ℝ)⟯
      OrbitFiberProduct μ c (Module.finBasis ℝ (GroupLieAlgebra I G)) :=
  letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  letI := h.orbitFiberProductChartedSpace c hreg (Module.finBasis ℝ (GroupLieAlgebra I G))
  { toEquiv := h.levelEquivOrbitFiberProduct
    contMDiff_toFun :=
      (h.isSmoothEmbedding_coe_orbitFiberProduct hreg _).contMDiff_iff_comp.2
        ((h.prod_neg_coadjointOrbitForm c).isSmoothEmbedding_coe_levelSubMulAction
          (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀).contMDiff
    contMDiff_invFun :=
      ((h.prod_neg_coadjointOrbitForm c).isSmoothEmbedding_coe_levelSubMulAction
        (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg)
          hn₀).contMDiff_iff_comp.2 (h.isSmoothEmbedding_coe_orbitFiberProduct hreg _).contMDiff }

/-- The map `Ψ⁻¹(0) → μ⁻¹(c) ⧸ G_c`, `(x, g G_c) ↦ [g⁻¹ • x]`, is a smooth submersion: it is the
orbit projection of the orbit fibre product read through the identification of points. -/
private theorem isSubmersion_orbitFiberProductProj_comp_levelEquiv :
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    IsSubmersion 𝓘(ℝ, Fin n₀ → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)) ∞
      (h.orbitFiberProductProj c (Module.finBasis ℝ (GroupLieAlgebra I G)) ∘
        h.levelEquivOrbitFiberProduct) := by
  let _ := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  have := (h.prod_neg_coadjointOrbitForm c).isManifold_levelSubMulAction
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  let _ := h.orbitFiberProductChartedSpace c hreg (Module.finBasis ℝ (GroupLieAlgebra I G))
  have := h.isManifold_orbitFiberProduct hreg (Module.finBasis ℝ (GroupLieAlgebra I G))
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  have hq := h.isSubmersion_orbitFiberProductProj hreg hn d
    (Module.finBasis ℝ (GroupLieAlgebra I G))
  set j := h.levelDiffeomorphOrbitFiberProduct hreg hn₀
  refine (ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv
    (hq.contMDiff.comp j.contMDiff) (by simp) fun p ↦ ?_).isSubmersion
  exact LinearMap.range_eq_top.1 ((j.range_mfderiv_comp_diffeomorph (by simp) _ p).trans
    (LinearMap.range_eq_top.2 (hq.surjective_mfderiv (by simp) _)))

omit [I'.Boundaryless] [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- The fibres of `(x, g G_c) ↦ [g⁻¹ • x]` on the zero level of the shifting moment map are the
orbits of the coadjoint stabilizer `G_0`, which is all of `G`. -/
private theorem orbitFiberProductProj_levelEquiv_eq_iff
    (p p' : (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) :
    h.orbitFiberProductProj c _ (h.levelEquivOrbitFiberProduct p) =
        h.orbitFiberProductProj c _ (h.levelEquivOrbitFiberProduct p') ↔
      ∃ k : (Lie.coadjointRepresentation ℝ I G).stabilizer 0, k • p' = p := by
  rw [h.orbitFiberProductProj_eq_orbitFiberProductProj_iff, coe_levelEquivOrbitFiberProduct,
    coe_levelEquivOrbitFiberProduct]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨⟨k⁻¹, Representation.mem_stabilizer.2 (map_zero _)⟩, Subtype.ext ?_⟩
    rw [SubMulAction.val_smul, Subgroup.smul_def]
    exact inv_smul_eq_iff.2 hk.symm
  · rintro ⟨k, rfl⟩
    exact ⟨(k : G)⁻¹, by rw [SubMulAction.val_smul, Subgroup.smul_def, inv_smul_smul]⟩

omit [I'.Boundaryless] [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- The bijection `Ψ⁻¹(0) ⧸ G_0 ≃ μ⁻¹(c) ⧸ G_c`, `[(x, g G_c)] ↦ [g⁻¹ • x]`, induced by the
map `(x, g G_c) ↦ [g⁻¹ • x]`, which is onto and has the `G_0`-orbits as fibres. -/
private def shiftingReducedSpaceEquiv :
    MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer 0)
        ((h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) ≃
      MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c) :=
  (Quotient.congrRight fun p p' ↦ (h.orbitFiberProductProj_levelEquiv_eq_iff p p').symm).trans
    (Setoid.quotientKerEquivOfSurjective _
      ((h.orbitFiberProductProj_surjective _).comp h.levelEquivOrbitFiberProduct.surjective))

variable (c) in
/-- **The shifting diffeomorphism of reduced spaces.** With the hypotheses of the
Marsden–Weinstein–Meyer theorem at `c` (`G` acts properly on `M`, `c` is a regular value of the
coadjoint-equivariant moment map `μ`, and `G_c`, with the Lie group structure `d`, acts freely on
the level `μ⁻¹(c)`), and any Lie group structure `d₀` on the coadjoint stabilizer `G_0` of zero,
the map

`Φ : Ψ⁻¹(0) ⧸ G_0 ≃ μ⁻¹(c) ⧸ G_c`, `Φ [(x, g G_c)] = [g⁻¹ • x]`

(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.shiftingReducedSpaceDiffeomorph_mk`) is a
diffeomorphism from the reduced space of `M × O⁻` at zero, for the shifting moment map
`Ψ(x, o) = μ(x) - ι_O(o)`, onto the reduced space of `M` at `c`. Its inverse sends `[z]` to the
orbit of `(z, G_c)`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.shiftingReducedSpaceDiffeomorph_symm_mk`). -/
def shiftingReducedSpaceDiffeomorph :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
    letI := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer 0)
        ((h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) ≃ₘ⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace F₀ (Fin n₀ → ℝ)),
      𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))⟯
      MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c) :=
  haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  haveI := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
  letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  letI := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
  letI := h.orbitRelQuotientChartedSpace c hreg hn d
  -- Smoothness of `Φ` and of its inverse is checked on the two surjective submersions out of
  -- `Ψ⁻¹(0)`: the orbit projection, and `(x, g G_c) ↦ [g⁻¹ • x]`.
  h.shiftingReducedSpaceEquiv.diffeomorphOfSubmersions
    ((h.prod_neg_coadjointOrbitForm c).isSubmersion_quotientMk_levelSubMulAction
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀)
    Quotient.mk_surjective (h.isSubmersion_orbitFiberProductProj_comp_levelEquiv hreg hn d hn₀)
    (funext fun _ ↦ rfl)

/-- The shifting diffeomorphism sends the orbit of `p` to the image of `p` under
`(x, g G_c) ↦ [g⁻¹ • x]`. -/
private theorem shiftingReducedSpaceDiffeomorph_quotientMk
    (p : (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
    letI := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    h.shiftingReducedSpaceDiffeomorph c hreg hn d hn₀ d₀ (Quotient.mk _ p) =
      h.orbitFiberProductProj c _ (h.levelEquivOrbitFiberProduct p) := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
  let _ := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  let _ := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  exact Equiv.diffeomorphOfSubmersions_apply _ _ _ _ _ _

/-- **The formula for the shifting diffeomorphism**: `Φ [(x, g G_c)] = [g⁻¹ • x]`. -/
@[simp]
theorem shiftingReducedSpaceDiffeomorph_mk (x : M) (g : G)
    (hx : ((x, (g : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)) :
      M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) ∈
        (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
    letI := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    h.shiftingReducedSpaceDiffeomorph c hreg hn d hn₀ d₀ (Quotient.mk _ ⟨_, hx⟩) =
      Quotient.mk _ ⟨g⁻¹ • x, h.mem_levelSubMulAction.2 (h.apply_eq_orbitMap_iff.1
        (h.mem_levelSubMulAction_prod_neg_coadjointOrbitForm.1 hx))⟩ :=
  (h.shiftingReducedSpaceDiffeomorph_quotientMk hreg hn d hn₀ d₀ _).trans
    (h.orbitFiberProductProj_eq _ _ rfl)

/-- **The inverse of the shifting diffeomorphism** sends the orbit `[z]` of a point `z` of the
level `μ⁻¹(c)` to the orbit of `(z, G_c)`. -/
@[simp]
theorem shiftingReducedSpaceDiffeomorph_symm_mk (z : h.levelSubMulAction c) :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
    letI := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    (h.shiftingReducedSpaceDiffeomorph c hreg hn d hn₀ d₀).symm (Quotient.mk _ z) =
      Quotient.mk _ ⟨((z : M), ((1 : G) : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)),
        h.mem_levelSubMulAction_prod_neg_coadjointOrbitForm.2 ((h.apply_eq_orbitMap_iff (g := 1)).2
          (by simpa using h.mem_levelSubMulAction.1 z.property))⟩ := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
  let _ := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  rw [← Diffeomorph.toEquiv_coe_symm, Equiv.symm_apply_eq, Diffeomorph.coe_toEquiv,
    shiftingReducedSpaceDiffeomorph_mk]
  exact congrArg _ (Subtype.ext (by simp))

omit [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- Read on the zero level of the shifting moment map, the form `pr_M^* σ - pr_O^* ω_KKS` of the
orbit fibre product is the restriction of the product form `σ ⊞ (-ω_KKS)`. -/
private theorem mpullback_levelDiffeomorphOrbitFiberProduct_sub :
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    haveI := (h.prod_neg_coadjointOrbitForm c).isManifold_levelSubMulAction
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    letI := h.orbitFiberProductChartedSpace c hreg (Module.finBasis ℝ (GroupLieAlgebra I G))
    haveI := h.isManifold_orbitFiberProduct hreg (Module.finBasis ℝ (GroupLieAlgebra I G))
    SmoothForm.mpullback (h.levelDiffeomorphOrbitFiberProduct hreg hn₀)
        (h.levelDiffeomorphOrbitFiberProduct hreg hn₀).contMDiff
        (SmoothForm.mpullback
            (fun p : OrbitFiberProduct μ c (Module.finBasis ℝ (GroupLieAlgebra I G)) ↦ p.val.1)
            (contMDiff_fst.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg _).contMDiff) σ -
          SmoothForm.mpullback
            (fun p : OrbitFiberProduct μ c (Module.finBasis ℝ (GroupLieAlgebra I G)) ↦ p.val.2)
            (contMDiff_snd.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg _).contMDiff)
            c.coadjointOrbitForm) =
      SmoothForm.mpullback Subtype.val
        ((h.prod_neg_coadjointOrbitForm c).isSmoothEmbedding_coe_levelSubMulAction
          (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀).contMDiff
        (σ.prod (-c.coadjointOrbitForm)) := by
  let _ := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  have := (h.prod_neg_coadjointOrbitForm c).isManifold_levelSubMulAction
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  let _ := h.orbitFiberProductChartedSpace c hreg (Module.finBasis ℝ (GroupLieAlgebra I G))
  have := h.isManifold_orbitFiberProduct hreg (Module.finBasis ℝ (GroupLieAlgebra I G))
  have hi₀ := ((h.prod_neg_coadjointOrbitForm c).isSmoothEmbedding_coe_levelSubMulAction
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀).contMDiff
  have hi := (h.isSmoothEmbedding_coe_orbitFiberProduct hreg
    (Module.finBasis ℝ (GroupLieAlgebra I G))).contMDiff
  set j := h.levelDiffeomorphOrbitFiberProduct hreg hn₀
  -- The identification `j` is the identity of points, so `pr_M ∘ j` and `pr_O ∘ j` are the two
  -- projections of `M × O` restricted to the zero level.
  rw [LinearMap.map_sub, SmoothForm.mpullback_mpullback_of_comp_eq
      (g := fun p : OrbitFiberProduct μ c (Module.finBasis ℝ (GroupLieAlgebra I G)) ↦ p.val.1)
      (g' := Prod.fst) j.contMDiff (contMDiff_fst.comp hi) hi₀ contMDiff_fst rfl,
    SmoothForm.mpullback_mpullback_of_comp_eq
      (g := fun p : OrbitFiberProduct μ c (Module.finBasis ℝ (GroupLieAlgebra I G)) ↦ p.val.2)
      (g' := Prod.snd) j.contMDiff (contMDiff_snd.comp hi) hi₀ contMDiff_snd rfl,
    congrArg (SmoothForm.mpullback Subtype.val hi₀) (prod_def σ (-c.coadjointOrbitForm)),
    LinearMap.map_add, LinearMap.map_neg, LinearMap.map_neg, sub_eq_add_neg]

/-- **The shifting theorem.** Let a Lie group `G` act smoothly and properly on `(M, σ)`, preserving
`σ`, with coadjoint-equivariant moment map `μ`, let `c` be a regular value of `μ` whose coadjoint
stabilizer `G_c` acts freely on the level `μ⁻¹(c)`, and let `O = G ⧸ G_c` be its coadjoint orbit.
Then the shifting diffeomorphism

`Φ : Ψ⁻¹(0) ⧸ G_0 ≃ μ⁻¹(c) ⧸ G_c`, `Φ [(x, g G_c)] = [g⁻¹ • x]`

from the reduced space of `M × O⁻` at zero, for `Ψ(x, o) = μ(x) - ι_O(o)` and the product form
`σ ⊞ (-ω_KKS)`, onto the reduced space of `M` at `c` pulls the reduced form `η` of `M` at `c`,
characterized by `π^* η = i^* σ`, back to the reduced form `η₀` of `M × O⁻` at zero, characterized
by `π₀^* η₀ = i₀^* (σ ⊞ (-ω_KKS))`. For a symplectic `σ`, these are the reduced symplectic forms of
the Marsden–Weinstein–Meyer theorem
(`existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback`, in the namespace
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`), so `Φ` is a symplectomorphism: reduction at `c`
is reduction of `M × O⁻` at zero. -/
theorem mpullback_shiftingReducedSpaceDiffeomorph
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    haveI := (h.prod_neg_coadjointOrbitForm c).isManifold_levelSubMulAction
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    letI := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
    haveI := (h.prod_neg_coadjointOrbitForm c).isManifold_orbitRelQuotient
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
    letI := h.levelSubMulActionChartedSpace c hreg hn
    haveI := h.isManifold_levelSubMulAction hreg hn
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    ∀ (η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c)))
      (η₀ : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F₀ (Fin n₀ → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer 0)
          ((h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0))),
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff σ →
        SmoothForm.mpullback _
            ((h.prod_neg_coadjointOrbitForm c).isSubmersion_quotientMk_levelSubMulAction
              (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
                d₀).contMDiff η₀ =
          SmoothForm.mpullback Subtype.val
            ((h.prod_neg_coadjointOrbitForm c).isSmoothEmbedding_coe_levelSubMulAction
              (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀).contMDiff
            (σ.prod (-c.coadjointOrbitForm)) →
        SmoothForm.mpullback _ (h.shiftingReducedSpaceDiffeomorph c hreg hn d hn₀ d₀).contMDiff η =
          η₀ := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
  let _ := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  have := (h.prod_neg_coadjointOrbitForm c).isManifold_levelSubMulAction
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  let _ := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
  have := (h.prod_neg_coadjointOrbitForm c).isManifold_orbitRelQuotient
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
  let _ := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  intro η η₀ hη hη₀
  set b := Module.finBasis ℝ (GroupLieAlgebra I G)
  let _ := h.orbitFiberProductChartedSpace c hreg b
  have := h.isManifold_orbitFiberProduct hreg b
  have hπ₀ := (h.prod_neg_coadjointOrbitForm c).isSubmersion_quotientMk_levelSubMulAction
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
  have hq := h.isSubmersion_orbitFiberProductProj hreg hn d b
  set j := h.levelDiffeomorphOrbitFiberProduct hreg hn₀
  -- `Φ ∘ π₀ = q_W ∘ j`, where `j` identifies `Ψ⁻¹(0)` with the orbit fibre product, on which the
  -- reduced form of `M` pulls back to `pr_M^* σ - pr_O^* ω_KKS`.
  have hk : ⇑(h.shiftingReducedSpaceDiffeomorph c hreg hn d hn₀ d₀) ∘ Quotient.mk _ =
      h.orbitFiberProductProj c b ∘ j :=
    funext (h.shiftingReducedSpaceDiffeomorph_quotientMk hreg hn d hn₀ d₀)
  have hqW :=
    (h.mpullback_quotientMk_eq_iff_mpullback_orbitFiberProductProj_eq_sub hreg hn d b hG η).1 hη
  -- Pullback along the surjective submersion `π₀` is injective.
  refine SmoothForm.mpullback_injective_of_surjective hπ₀.contMDiff Quotient.mk_surjective
    (hπ₀.surjective_mfderiv (by simp)) ?_
  rw [hη₀, SmoothForm.mpullback_mpullback_of_comp_eq hπ₀.contMDiff
    (h.shiftingReducedSpaceDiffeomorph c hreg hn d hn₀ d₀).contMDiff j.contMDiff hq.contMDiff hk,
    hqW]
  exact h.mpullback_levelDiffeomorphOrbitFiberProduct_sub hreg hn₀

end Reduced

end TauCeti.SmoothTwoForm.IsEquivariantMomentMap
