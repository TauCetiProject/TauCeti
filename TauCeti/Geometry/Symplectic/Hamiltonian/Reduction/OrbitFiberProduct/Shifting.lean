/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Prod
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.OrbitFiberProduct.ReducedForm

import TauCeti.Geometry.Manifold.Diffeomorph.Subtype
import TauCeti.Geometry.Manifold.Submersion.Diffeomorph
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Naturality
import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.OrbitFiberProduct.Quotient

/-!
# The shifting theorem: reduction at `c` is reduction of `M × O⁻` at zero

Let a Lie group `G` act smoothly and properly on a manifold `M` with a two-form `σ` and a
coadjoint-equivariant moment map `μ : M → 𝔤*`, let `c` be a regular value of `μ` at which the
coadjoint stabilizer `G_c` acts freely on the level `μ⁻¹(c)`, and let `O = G ⧸ G_c` be the coadjoint
orbit of `c`, with its Kirillov–Kostant–Souriau form `ω_KKS` and orbit map `ι_O [g] = Ad*_g c`.
Write `M × O⁻` for `M × O` with the diagonal action of `G` and the form `σ ⊞ (-ω_KKS)`.

* The **shifting map** `Ψ(x, o) = μ(x) - ι_O(o)` is a coadjoint-equivariant moment map of
  `M × O⁻` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prod_neg_coadjointOrbitForm`).
* Zero is a regular value of `Ψ`
  (`IsEquivariantMomentMap.differential_prod_neg_coadjointOrbitForm_surjective`), and the
  stabilizer `G_0 = G` of zero acts freely on `Ψ⁻¹(0)`
  (`IsEquivariantMomentMap.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm`).
  So the Marsden–Weinstein–Meyer theorem applies to `M × O⁻` at zero, and gives the reduced space
  `Ψ⁻¹(0) ⧸ G` with its reduced form.
* **The shifting theorem.** The map `[(x, g G_c)] ↦ [g⁻¹ • x]` is a diffeomorphism

  `Φ : Ψ⁻¹(0) ⧸ G ≃ μ⁻¹(c) ⧸ G_c`, with inverse `[z] ↦ [(z, G_c)]`

  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.shiftingReducedSpaceDiffeomorph`), for the
  atlases of the Marsden–Weinstein–Meyer theorem on both sides, and it pulls the reduced form of
  `μ⁻¹(c) ⧸ G_c` back to the reduced form of `Ψ⁻¹(0) ⧸ G`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback_shiftingReducedSpaceDiffeomorph`).
  So reducing `M` at `c` and reducing `M × O⁻` at zero give symplectomorphic reduced spaces.

The zero level `Ψ⁻¹(0)` is the orbit fibre product `W_O = {(x, o) | μ(x) = ι_O(o)}`, and `Φ` is
induced by its orbit projection `q_W (x, g G_c) = [g⁻¹ • x]`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductProj`), a surjective submersion
whose fibres are the `G`-orbits. The comparison of the reduced forms uses the section
`z ↦ (z, G_c)` of `Ψ⁻¹(0)` over `μ⁻¹(c)`, along which `σ ⊞ (-ω_KKS)` restricts to the restriction
of `σ`, as the second component of the section is constant.

## Main definitions

* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.shiftingReducedSpaceDiffeomorph`: the
  diffeomorphism `Ψ⁻¹(0) ⧸ G ≃ μ⁻¹(c) ⧸ G_c`.

## Main results

* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prod_neg_coadjointOrbitForm`: `Ψ` is a
  coadjoint-equivariant moment map of `M × O⁻`.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.shiftingReducedSpaceDiffeomorph_quotientMk`:
  `Φ` is the descent of the orbit projection `q_W`, `Φ [z] = q_W z`.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.shiftingReducedSpaceDiffeomorph_mk`,
  `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.shiftingReducedSpaceDiffeomorph_symm_mk`: the
  formulas `Φ [(x, g G_c)] = [g⁻¹ • x]` and `Φ⁻¹ [z] = [(z, G_c)]`.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback_shiftingReducedSpaceDiffeomorph`: the
  shifting theorem, `Φ^* ω_red = ω_red⁰`.

## References

* E. Meinrenken, *Symplectic geometry*, lecture notes, University of Toronto, 2000,
  Proposition 8.6 (the shifting trick).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 24.4 (reduction at other levels, for compact groups).
* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 6.1 (orbit reduction and the shifting theorem).
-/

public section

noncomputable section

open Function Module Manifold
open scoped Manifold ContDiff

namespace TauCeti

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

namespace SmoothTwoForm

namespace IsEquivariantMomentMap

variable (h : σ.IsEquivariantMomentMap μ)

include h in
variable (c) in
/-- **The shifting map is a moment map of `M × O⁻`.** For a coadjoint-equivariant moment map `μ`
of `(M, σ)` and the coadjoint orbit `O = G ⧸ G_c` with its Kirillov–Kostant–Souriau form
`ω_KKS`, the shifting map `Ψ(x, o) = μ(x) - ι_O(o)` is a coadjoint-equivariant moment map of the
diagonal action of `G` on `M × O` with the form `σ ⊞ (-ω_KKS)`. -/
theorem prod_neg_coadjointOrbitForm :
    (σ.prod (-c.coadjointOrbitForm)).IsEquivariantMomentMap
      fun p : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c ↦
        μ p.1 - (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 := by
  simpa only [sub_eq_add_neg] using h.prod c.isEquivariantMomentMap_coadjointOrbitForm.neg

/-- **Zero is a regular value of the shifting moment map** `Ψ(x, o) = μ(x) - ι_O(o)` of `M × O⁻`
when `c` is a regular value of `μ`. -/
theorem differential_prod_neg_coadjointOrbitForm_surjective
    (hreg : ∀ x, μ x = c → Surjective (h.differential x))
    (p : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)
    (hp : μ p.1 - (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 = 0) :
    Surjective ((h.prod_neg_coadjointOrbitForm c).differential p) := by
  refine ((h.prod_neg_coadjointOrbitForm c).toIsMomentMap.isRegularPoint_components_iff
    (finBasis ℝ (GroupLieAlgebra I G))).1 ?_
  simpa only [LinearMap.sub_apply] using
    (h.isRegularValue_sub_orbitMap hreg (finBasis ℝ (GroupLieAlgebra I G))).isRegularPoint
      (funext fun i ↦ by simp [← LinearMap.sub_apply, hp])

variable [FiniteDimensional ℝ E']

/-- **The diagonal action is free on the zero level of the shifting map** when `G_c` acts freely
on the level `μ⁻¹(c)`: the zero level is the orbit fibre product, on which `G` acts freely. -/
theorem isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm
    [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] :
    IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer 0)
      ((h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) := by
  let b := finBasis ℝ (GroupLieAlgebra I G)
  let _ := h.orbitFiberProductMulAction c b
  have := h.isCancelSMul_orbitFiberProduct (c := c) b
  refine (h.prod_neg_coadjointOrbitForm c).isCancelSMul_levelSubMulAction fun p hp ↦ ?_
  refine (Subgroup.eq_bot_iff_forall _).2 fun k hk ↦ ?_
  let q : OrbitFiberProduct μ c b :=
    ⟨p, (components_eq_orbitMap_iff_apply_eq b).2 (sub_eq_zero.1 hp)⟩
  exact IsCancelSMul.eq_one_of_smul (G := G) (x := q)
    (Subtype.ext ((h.coe_smul_orbitFiberProduct b k q).trans (MulAction.mem_stabilizer_iff.1 hk)))

/-! ### The reduced space of `M × O⁻` at zero -/

section Reduced

variable [I'.Boundaryless] [ProperSMul G M]
  (hreg : ∀ x, μ x = c → Surjective (h.differential x))
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
  {n : ℕ} (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)
  {n₀ : ℕ} (hn₀ : finrank ℝ (E' × Subgroup.QuotientModelSpace I
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) - finrank ℝ (GroupLieAlgebra I G) = n₀)
  {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [FiniteDimensional ℝ F₀]
  (d₀ : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer 0) F₀)

omit [FiniteDimensional ℝ E'] [I'.Boundaryless] [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- A zero `(x, o)` of the shifting map lies in the orbit fibre product. -/
private theorem mem_orbitFiberProduct
    (z : (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) :
    z.val ∈ {p : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c |
      (fun i ↦ μ p.1 (finBasis ℝ (GroupLieAlgebra I G) i)) =
        fun i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2
          (finBasis ℝ (GroupLieAlgebra I G) i)} :=
  (components_eq_orbitMap_iff_apply_eq _).2
    (sub_eq_zero.1 ((h.prod_neg_coadjointOrbitForm c).mem_levelSubMulAction.1 z.property))

/-- The zero level of the shifting moment map, with its regular-level atlas, is the orbit fibre
product with its transverse fibre-product atlas: the identity of points is a diffeomorphism. -/
private def levelDiffeomorphOrbitFiberProduct :
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀
    letI := h.orbitFiberProductChartedSpace c hreg (finBasis ℝ (GroupLieAlgebra I G))
    (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0 ≃ₘ⟮𝓘(ℝ, Fin n₀ → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ (Subgroup.QuotientModelSpace I
        ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (Fin (finrank ℝ (GroupLieAlgebra I G)) → ℝ)) → ℝ)⟯
      OrbitFiberProduct μ c (finBasis ℝ (GroupLieAlgebra I G)) :=
  letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀
  letI := h.orbitFiberProductChartedSpace c hreg (finBasis ℝ (GroupLieAlgebra I G))
  -- Both atlases make the inclusion into `M × G ⧸ G_c` a smooth embedding, so the identity of
  -- `M × G ⧸ G_c` restricts to a diffeomorphism between them.
  (Diffeomorph.refl _ (M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)
    ∞).subtypeOfIsSmoothEmbedding
    (s := ((h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0 : Set _))
    (t := {p | (fun i ↦ μ p.1 (finBasis ℝ (GroupLieAlgebra I G) i)) =
      fun i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2
        (finBasis ℝ (GroupLieAlgebra I G) i)})
    ((h.prod_neg_coadjointOrbitForm c).isSmoothEmbedding_coe_levelSubMulAction
      (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀)
    (h.isSmoothEmbedding_coe_orbitFiberProduct hreg _) fun _ ↦ by
      simp [components_eq_orbitMap_iff_apply_eq, sub_eq_zero]

variable (c) in
/-- The orbit projection `(x, g G_c) ↦ [g⁻¹ • x]` from the zero level of the shifting map onto the
reduced space `μ⁻¹(c) ⧸ G_c`: the orbit projection of the orbit fibre product. -/
private def zeroLevelProj (z : (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) :
    MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
      (h.levelSubMulAction c) :=
  h.orbitFiberProductProj c (finBasis ℝ (GroupLieAlgebra I G)) ⟨z.val, h.mem_orbitFiberProduct z⟩

omit [I'.Boundaryless] [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- The orbit projection of the zero level is onto the reduced space `μ⁻¹(c) ⧸ G_c`. -/
private theorem zeroLevelProj_surjective : Surjective (h.zeroLevelProj c) := fun w ↦ by
  obtain ⟨p, rfl⟩ := h.orbitFiberProductProj_surjective (finBasis ℝ (GroupLieAlgebra I G)) w
  exact ⟨⟨p.val, (h.prod_neg_coadjointOrbitForm c).mem_levelSubMulAction.2
    (sub_eq_zero.2 ((components_eq_orbitMap_iff_apply_eq _).1 p.property))⟩, rfl⟩

omit [I'.Boundaryless] [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- The fibres of the orbit projection of the zero level are the orbits of `G_0 = G`. -/
private theorem zeroLevelProj_eq_zeroLevelProj_iff
    (z z' : (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) :
    h.zeroLevelProj c z = h.zeroLevelProj c z' ↔
      MulAction.orbitRel ((Lie.coadjointRepresentation ℝ I G).stabilizer 0)
        ((h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) z z' := by
  simp only [zeroLevelProj]
  rw [orbitFiberProductProj_eq_orbitFiberProductProj_iff, orbitRel_levelSubMulAction_iff,
    MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k⁻¹, inv_smul_eq_iff.2 hk.symm⟩
  · rintro ⟨k, hk⟩
    exact ⟨k⁻¹, inv_smul_eq_iff.2 hk.symm⟩

/-- The orbit projection of the zero level onto the reduced space `μ⁻¹(c) ⧸ G_c` is a smooth
submersion: it is the orbit projection of the orbit fibre product, read through the identity of
points of the zero level with the orbit fibre product. -/
private theorem isSubmersion_zeroLevelProj :
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    IsSubmersion 𝓘(ℝ, Fin n₀ → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)) ∞
      (h.zeroLevelProj c) := by
  let _ := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀
  have := (h.prod_neg_coadjointOrbitForm c).isManifold_levelSubMulAction
    (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀
  let _ := h.orbitFiberProductChartedSpace c hreg (finBasis ℝ (GroupLieAlgebra I G))
  have := h.isManifold_orbitFiberProduct hreg (finBasis ℝ (GroupLieAlgebra I G))
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  have hq := h.isSubmersion_orbitFiberProductProj hreg hn d (finBasis ℝ (GroupLieAlgebra I G))
  set ι := h.levelDiffeomorphOrbitFiberProduct hreg hn₀
  -- `zeroLevelProj = q_W ∘ ι`, as `ι` is the identity on points, and precomposing the submersion
  -- `q_W` with the diffeomorphism `ι` keeps the differentials onto.
  have hι : h.zeroLevelProj c = h.orbitFiberProductProj c _ ∘ ι :=
    funext fun z ↦ congrArg (h.orbitFiberProductProj c _) (Subtype.ext
      (Diffeomorph.subtypeOfIsSmoothEmbedding_apply_coe (Diffeomorph.refl _ _ ∞) _ _ _ z).symm)
  rw [hι]
  refine (ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv
    (hq.contMDiff.comp ι.contMDiff) (by simp) fun z ↦ ?_).isSubmersion
  exact LinearMap.range_eq_top.1 ((ι.range_mfderiv_comp_diffeomorph (by simp) _ z).trans
    (LinearMap.range_eq_top.2 (hq.surjective_mfderiv (by simp) _)))

/-- **The shifting theorem: the diffeomorphism.** Let a Lie group `G` act smoothly and properly on
`M` with coadjoint-equivariant moment map `μ`, let `c` be a regular value of `μ` at which `G_c`
acts freely on the level, and let `O = G ⧸ G_c` be the coadjoint orbit of `c`. The reduced space
of `M × O` at zero, for the shifting moment map `Ψ(x, o) = μ(x) - ι_O(o)`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.prod_neg_coadjointOrbitForm`), is diffeomorphic to
the reduced space `μ⁻¹(c) ⧸ G_c`, by

`[(x, g G_c)] ↦ [g⁻¹ • x]`, with inverse `[z] ↦ [(z, G_c)]`

(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.shiftingReducedSpaceDiffeomorph_mk`,
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.shiftingReducedSpaceDiffeomorph_symm_mk`). Both
reduced spaces carry the atlases of the Marsden–Weinstein–Meyer theorem; zero is a regular value of
`Ψ` and `G` acts freely on `Ψ⁻¹(0)`
(`IsEquivariantMomentMap.differential_prod_neg_coadjointOrbitForm_surjective`,
`IsEquivariantMomentMap.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm`).
-/
def shiftingReducedSpaceDiffeomorph :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
    letI := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
      (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀ d₀
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
    (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀
  letI := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
    (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀ d₀
  letI := h.orbitRelQuotientChartedSpace c hreg hn d
  -- `ProperSMul.diffeomorphOfOrbitSubmersion` does not apply: its source carries the atlas
  -- `ProperSMul.orbitRelQuotientChartedSpace`, and the body of `orbitRelQuotientChartedSpace`
  -- that unfolds to it is not exposed here. So descend `zeroLevelProj` through the submersion
  -- lemmas stated for the exposed atlases.
  Equiv.diffeomorphOfSubmersions
    ((Quotient.congrRight fun z z' ↦ (h.zeroLevelProj_eq_zeroLevelProj_iff z z').symm).trans
      (Setoid.quotientKerEquivOfSurjective _ h.zeroLevelProj_surjective))
    ((h.prod_neg_coadjointOrbitForm c).isSubmersion_quotientMk_levelSubMulAction
      (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀ d₀)
    Quotient.mk_surjective (h.isSubmersion_zeroLevelProj hreg hn d hn₀) (funext fun _ ↦ rfl)

/-- **The shifting diffeomorphism is the descent of the orbit projection** `q_W`: it sends the
orbit of a zero `z` of the shifting map to `q_W z`, reading `z` as a point of the orbit fibre
product `W_O` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductProj`). -/
@[simp]
theorem shiftingReducedSpaceDiffeomorph_quotientMk
    (z : (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
    letI := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
      (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀ d₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    h.shiftingReducedSpaceDiffeomorph hreg hn d hn₀ d₀ (Quotient.mk _ z) =
      h.orbitFiberProductProj c (finBasis ℝ (GroupLieAlgebra I G))
        ⟨z.val, (components_eq_orbitMap_iff_apply_eq _).2 (sub_eq_zero.1
          ((h.prod_neg_coadjointOrbitForm c).mem_levelSubMulAction.1 z.property))⟩ := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
  let _ := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀
  let _ := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
    (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀ d₀
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  -- The underlying bijection computes on orbits by `Quotient.congrRight` and
  -- `Setoid.quotientKerEquivOfSurjective`, both of which send `[z]` to `zeroLevelProj z`.
  exact Equiv.diffeomorphOfSubmersions_apply _ _ _ _ _ _

/-- The shifting diffeomorphism sends the orbit of `(x, g G_c)` to the orbit of `g⁻¹ • x`. -/
theorem shiftingReducedSpaceDiffeomorph_mk (x : M) (g : G)
    (hp : (x, (g : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)) ∈
      (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
    letI := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
      (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀ d₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    h.shiftingReducedSpaceDiffeomorph hreg hn d hn₀ d₀ (Quotient.mk _ ⟨(x, g), hp⟩) =
      Quotient.mk _ ⟨g⁻¹ • x, h.mem_levelSubMulAction.2 (h.apply_eq_orbitMap_iff.1
        (sub_eq_zero.1 ((h.prod_neg_coadjointOrbitForm c).mem_levelSubMulAction.1 hp)))⟩ :=
  (h.shiftingReducedSpaceDiffeomorph_quotientMk hreg hn d hn₀ d₀ _).trans
    (h.orbitFiberProductProj_mk _ _ _ _)

/-- The inverse of the shifting diffeomorphism sends the orbit of `z` to the orbit of
`(z, G_c)`. -/
@[simp]
theorem shiftingReducedSpaceDiffeomorph_symm_mk (z : h.levelSubMulAction c) :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
    letI := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
      (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀ d₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    (h.shiftingReducedSpaceDiffeomorph hreg hn d hn₀ d₀).symm (Quotient.mk _ z) =
      Quotient.mk _ ⟨((z : M), ((1 : G) : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)),
        (h.prod_neg_coadjointOrbitForm c).mem_levelSubMulAction.2 (sub_eq_zero.2
          (h.apply_eq_orbitMap_iff.2 (by simpa using h.mem_levelSubMulAction.1 z.property)))⟩ := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
  let _ := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
    (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀ d₀
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  apply (h.shiftingReducedSpaceDiffeomorph hreg hn d hn₀ d₀).injective
  rw [Diffeomorph.coe_toEquiv, Diffeomorph.apply_symm_apply, shiftingReducedSpaceDiffeomorph_mk]
  exact congrArg _ (Subtype.ext (by simp))

omit [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- Along the section `z ↦ (z, G_c)` of the zero level of the shifting map over the level
`μ⁻¹(c)`, the form `σ ⊞ (-ω_KKS)` of `M × O` pulls back to the restriction of `σ`, since the second
component of the section is constant. -/
private theorem mpullback_prodMk_one_prod_neg_coadjointOrbitForm :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    haveI := h.isManifold_levelSubMulAction hreg hn
    SmoothForm.mpullback
        (fun z : h.levelSubMulAction c ↦
          ((z : M), ((1 : G) : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)))
        ((h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff.prodMk contMDiff_const)
        (σ.prod (-c.coadjointOrbitForm)) =
      SmoothForm.mpullback Subtype.val (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
        σ := by
  let _ := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  rw [prod_def, map_add, SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback]
  -- The first summand is the right-hand side: `Prod.fst ∘ (fun z ↦ (↑z, 1))` is `Subtype.val` by
  -- unfolding `Function.comp` and `Prod.fst`, so it remains to kill the second summand.
  refine add_eq_left.2 (Subtype.ext ?_)
  rw [SmoothForm.coe_mpullback]
  exact mpullback_const two_ne_zero _ _

/-- **The shifting theorem.** Let a Lie group `G` act smoothly and properly on `(M, σ)` with
coadjoint-equivariant moment map `μ`, let `c` be a regular value of `μ` at which `G_c` acts freely
on the level, and let `O = G ⧸ G_c` be the coadjoint orbit of `c`, with its
Kirillov–Kostant–Souriau form `ω_KKS`. Reduction of `M` at `c` is reduction at zero of
`M × O⁻ = (M × O, σ ⊞ (-ω_KKS))`, for the shifting moment map `Ψ(x, o) = μ(x) - ι_O(o)`: the
diffeomorphism `[(x, g G_c)] ↦ [g⁻¹ • x]` of reduced spaces
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.shiftingReducedSpaceDiffeomorph`) pulls a reduced
form `η` of `μ⁻¹(c) ⧸ G_c`, characterized by `π^* η = i^* σ`, back to the reduced form `η₀` of
`Ψ⁻¹(0) ⧸ G`, characterized by `π₀^* η₀ = i₀^* (σ ⊞ (-ω_KKS))`. In particular the
Marsden–Weinstein–Meyer reduced spaces of `M` at `c` and of `M × O⁻` at zero are symplectomorphic.
Neither closedness nor nondegeneracy of `σ`, nor invariance of `σ`, is needed for this
comparison. -/
theorem mpullback_shiftingReducedSpaceDiffeomorph :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    letI := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
      (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀ d₀
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := (h.prod_neg_coadjointOrbitForm c).isManifold_levelSubMulAction
      (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    haveI := (h.prod_neg_coadjointOrbitForm c).isManifold_orbitRelQuotient
      (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀ d₀
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
              (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀ d₀).contMDiff η₀ =
          SmoothForm.mpullback Subtype.val
            ((h.prod_neg_coadjointOrbitForm c).isSmoothEmbedding_coe_levelSubMulAction
              (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀).contMDiff
            (σ.prod (-c.coadjointOrbitForm)) →
        SmoothForm.mpullback _ (h.shiftingReducedSpaceDiffeomorph hreg hn d hn₀ d₀).contMDiff η =
          η₀ := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
  let _ := h.levelSubMulActionChartedSpace c hreg hn
  let _ := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  let _ := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
    (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀ d₀
  have := h.isManifold_levelSubMulAction hreg hn
  have := (h.prod_neg_coadjointOrbitForm c).isManifold_levelSubMulAction
    (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀
  have := h.isManifold_orbitRelQuotient hreg hn d
  have := (h.prod_neg_coadjointOrbitForm c).isManifold_orbitRelQuotient
    (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀ d₀
  intro η η₀ hη hη₀
  have hπ := h.isSubmersion_quotientMk_levelSubMulAction hreg hn d
  have hπ₀ := (h.prod_neg_coadjointOrbitForm c).isSubmersion_quotientMk_levelSubMulAction
    (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀ d₀
  have hi := h.isSmoothEmbedding_coe_levelSubMulAction hreg hn
  have hi₀ := (h.prod_neg_coadjointOrbitForm c).isSmoothEmbedding_coe_levelSubMulAction
    (h.differential_prod_neg_coadjointOrbitForm_surjective hreg) hn₀
  -- The section `j z = (z, G_c)` of the zero level over the level `μ⁻¹(c)`; by the inverse
  -- formula, `Φ⁻¹ ∘ π = π₀ ∘ j`.
  let j : h.levelSubMulAction c → (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0 :=
    fun z ↦ ⟨((z : M), ((1 : G) : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)),
      (h.prod_neg_coadjointOrbitForm c).mem_levelSubMulAction.2 (sub_eq_zero.2
        (h.apply_eq_orbitMap_iff.2 (by simpa using h.mem_levelSubMulAction.1 z.property)))⟩
  have hj : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n₀ → ℝ) ∞ j :=
    hi₀.contMDiff_iff_comp.2 (hi.contMDiff.prodMk contMDiff_const)
  have hΦj : ⇑(h.shiftingReducedSpaceDiffeomorph hreg hn d hn₀ d₀).symm ∘ Quotient.mk _ =
      Quotient.mk _ ∘ j :=
    funext (h.shiftingReducedSpaceDiffeomorph_symm_mk hreg hn d hn₀ d₀)
  -- So `Φ⁻¹` carries `η₀` to `η`: `j` carries the restricted form of `M × O⁻` to that of `M`, and
  -- `Φ⁻¹ ∘ π = π₀ ∘ j`.
  have hsymm :=
    SmoothForm.mpullback_eq_of_mpullback_eq hi.contMDiff hπ.contMDiff hi₀.contMDiff hπ₀.contMDiff
      hη hη₀ Quotient.mk_surjective (hπ.surjective_mfderiv (by simp)) hj
      ((SmoothForm.mpullback_mpullback _ _ _ _ _).trans
        (h.mpullback_prodMk_one_prod_neg_coadjointOrbitForm hreg hn))
      (h.shiftingReducedSpaceDiffeomorph hreg hn d hn₀ d₀).symm.contMDiff hΦj
  rw [← hsymm, SmoothForm.mpullback_mpullback_symm]

end Reduced

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
