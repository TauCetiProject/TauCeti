/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Prod
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.OrbitFiberProduct.ReducedForm
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace

import TauCeti.Geometry.Manifold.Diffeomorph.Subtype
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.OrbitFiberProduct.Quotient

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

* `Ψ(x, o) = μ(x) - ι_O(o)` is a coadjoint-equivariant moment map of `σ ⊞ (-ω_KKS)` for the
  diagonal action of `G` on `M × O` (`prod_neg_coadjointOrbitForm`). Its zero level is the set
  of pairs with `μ(x) = ι_O(o)` (`mem_levelSubMulAction_prod_neg_coadjointOrbitForm`).
* Zero is a regular value of `Ψ` (`forall_differential_surjective_prod_neg_coadjointOrbitForm`),
  and the coadjoint stabilizer `G_0`, which is all of `G`, acts freely on `Ψ⁻¹(0)`
  (`isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm`):
  if `k` fixes `(x, g G_c)`, then `g⁻¹ k g` lies in `G_c` and fixes the point `g⁻¹ • x` of
  `μ⁻¹(c)`. So the Marsden–Weinstein–Meyer theorem applies to `M × O⁻` at zero.
* The map `Ψ⁻¹(0) → μ⁻¹(c) ⧸ G_c`, `(x, g G_c) ↦ [g⁻¹ • x]`, is a surjective smooth submersion
  whose fibres are the orbits of `G_0`: on points it is the orbit projection of the orbit fibre
  product `W_O`, whose transverse fibre-product atlas agrees with the regular-level atlas of
  `Ψ⁻¹(0)`: the identity of points is a diffeomorphism `j : Ψ⁻¹(0) ≃ W_O`
  (`levelDiffeomorphOrbitFiberProduct`). It therefore descends to a diffeomorphism of reduced
  spaces

  `Φ : Ψ⁻¹(0) ⧸ G_0 ≃ μ⁻¹(c) ⧸ G_c`, `Φ [(x, g G_c)] = [g⁻¹ • x]`

  (`shiftingReducedSpaceDiffeomorph`), with inverse `[z] ↦ [(z, G_c)]`, and `Φ ∘ π₀ = q_W ∘ j`
  for the orbit projections `π₀` of `Ψ⁻¹(0)` and `q_W` of `W_O`
  (`shiftingReducedSpaceDiffeomorph_comp_quotientMk`).
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
* `levelDiffeomorphOrbitFiberProduct`: the identity of points `j : Ψ⁻¹(0) ≃ W_O` is a
  diffeomorphism.
* `levelDiffeomorphShiftingLevel`: the identity of points is a diffeomorphism from `Ψ⁻¹(0)` to
  `TauCeti.ShiftingLevel`, the same zero level with `Ψ` read in a basis.
* `shiftingReducedSpaceDiffeomorph`, `shiftingReducedSpaceDiffeomorph_mk`,
  `shiftingReducedSpaceDiffeomorph_symm_mk`: the diffeomorphism of reduced spaces.
* `shiftingReducedSpaceDiffeomorph_comp_quotientMk`: `Φ ∘ π₀ = q_W ∘ j`.
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
  {κ : Type*} [Fintype κ] (b : Basis κ ℝ (GroupLieAlgebra I G))

omit [I'.Boundaryless] [ProperSMul G M] in
/-- **The coadjoint stabilizer of zero acts freely on the zero level of the shifting moment map**
when `G_c` acts freely on the level `μ⁻¹(c)`: the zero level is the orbit fibre product, on which
`G` acts freely (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isCancelSMul_orbitFiberProduct`). -/
theorem isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm :
    IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer 0)
      ((h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) := by
  let _ := h.orbitFiberProductMulAction c (Module.finBasis ℝ (GroupLieAlgebra I G))
  have := h.isCancelSMul_orbitFiberProduct (c := c) (Module.finBasis ℝ (GroupLieAlgebra I G))
  refine isCancelSMul_iff_eq_one_of_smul_eq.2 fun k p hk ↦ Subtype.ext ?_
  -- `k` fixes `p`, read as a point of the orbit fibre product.
  let q : OrbitFiberProduct μ c (Module.finBasis ℝ (GroupLieAlgebra I G)) :=
    ⟨p.val, (components_eq_orbitMap_iff_apply_eq _).2
      (h.mem_levelSubMulAction_prod_neg_coadjointOrbitForm.1 p.property)⟩
  have hk' : (k : G) • p.val = p.val := congrArg Subtype.val hk
  exact IsCancelSMul.eq_one_of_smul (x := q)
    (Subtype.ext ((h.coe_smul_orbitFiberProduct _ (k : G) q).trans hk'))

omit [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- **The zero level of the shifting moment map is the orbit fibre product.** The identity of
points is a diffeomorphism `j` from the regular-level atlas of the zero level `Ψ⁻¹(0)` of the
shifting moment map to the transverse fibre-product atlas of the orbit fibre product `W_O`, read in
a basis `b` of `𝔤`: both make the inclusion into `M × O` a smooth embedding. Composed with
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductDiffeomorphShiftingLevel`, it
identifies `Ψ⁻¹(0)` with `TauCeti.ShiftingLevel`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelDiffeomorphShiftingLevel`). -/
def levelDiffeomorphOrbitFiberProduct :
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    letI := h.orbitFiberProductChartedSpace c hreg b
    (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0 ≃ₘ⟮𝓘(ℝ, Fin n₀ → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ (Subgroup.QuotientModelSpace I
        ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ)⟯
      OrbitFiberProduct μ c b :=
  letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  letI := h.orbitFiberProductChartedSpace c hreg b
  (Diffeomorph.refl _ (M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)
    ∞).subtypeOfIsSmoothEmbedding
    (s := ((h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0 :
      Set (M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)))
    (t := {p | (fun i ↦ μ p.1 (b i)) =
      fun i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 (b i)})
    ((h.prod_neg_coadjointOrbitForm c).isSmoothEmbedding_coe_levelSubMulAction
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀)
    (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b) fun _ ↦
      h.mem_levelSubMulAction_prod_neg_coadjointOrbitForm.trans
        (components_eq_orbitMap_iff_apply_eq _).symm

omit [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- The identification of the zero level of the shifting moment map with the orbit fibre product
is the identity of points. -/
@[simp]
theorem coe_levelDiffeomorphOrbitFiberProduct
    (p : (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) :
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    letI := h.orbitFiberProductChartedSpace c hreg b
    (h.levelDiffeomorphOrbitFiberProduct hreg hn₀ b p :
        M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) = p.val := by
  let _ := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  let _ := h.orbitFiberProductChartedSpace c hreg b
  exact Diffeomorph.subtypeOfIsSmoothEmbedding_apply_coe ..

omit [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- The inverse identification of the orbit fibre product with the zero level of the shifting
moment map is the identity of points. -/
@[simp]
theorem coe_levelDiffeomorphOrbitFiberProduct_symm
    (q : OrbitFiberProduct μ c b) :
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    letI := h.orbitFiberProductChartedSpace c hreg b
    ((h.levelDiffeomorphOrbitFiberProduct hreg hn₀ b).symm q :
        M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) = q.val := by
  let _ := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  let _ := h.orbitFiberProductChartedSpace c hreg b
  exact Diffeomorph.subtypeOfIsSmoothEmbedding_symm_apply_coe ..

omit [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- **The two models of the zero level of the shifting moment map agree.** The identity of points
is a diffeomorphism from the regular-level atlas of the zero level `Ψ⁻¹(0)` of the moment map `Ψ`
of `M × O⁻` to the regular-fibre atlas of `TauCeti.ShiftingLevel`, with `Ψ` read in a basis `b`
of `𝔤`: it is
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelDiffeomorphOrbitFiberProduct` followed by
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductDiffeomorphShiftingLevel`. -/
def levelDiffeomorphShiftingLevel :
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    letI := h.shiftingLevelChartedSpace c hreg b
    (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0 ≃ₘ⟮𝓘(ℝ, Fin n₀ → ℝ),
      𝓘(ℝ, Fin (finrank ℝ (E' × Subgroup.QuotientModelSpace I
        ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ)⟯
      ShiftingLevel μ c b :=
  letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  letI := h.orbitFiberProductChartedSpace c hreg b
  letI := h.shiftingLevelChartedSpace c hreg b
  (h.levelDiffeomorphOrbitFiberProduct hreg hn₀ b).trans
    (h.orbitFiberProductDiffeomorphShiftingLevel hreg b)

omit [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- The identification of the two models of the zero level of the shifting moment map is the
identity of points. -/
@[simp]
theorem coe_levelDiffeomorphShiftingLevel
    (p : (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) :
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    letI := h.shiftingLevelChartedSpace c hreg b
    (h.levelDiffeomorphShiftingLevel hreg hn₀ b p :
        M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) = p.val := by
  let _ := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  let _ := h.orbitFiberProductChartedSpace c hreg b
  let _ := h.shiftingLevelChartedSpace c hreg b
  exact (h.coe_orbitFiberProductDiffeomorphShiftingLevel hreg b _).trans
    (h.coe_levelDiffeomorphOrbitFiberProduct hreg hn₀ b p)

omit [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- The inverse identification of `TauCeti.ShiftingLevel` with the zero level of the shifting
moment map is the identity of points. -/
@[simp]
theorem coe_levelDiffeomorphShiftingLevel_symm (q : ShiftingLevel μ c b) :
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    letI := h.shiftingLevelChartedSpace c hreg b
    ((h.levelDiffeomorphShiftingLevel hreg hn₀ b).symm q :
        M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) = q.val := by
  let _ := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  let _ := h.orbitFiberProductChartedSpace c hreg b
  let _ := h.shiftingLevelChartedSpace c hreg b
  exact (h.coe_levelDiffeomorphOrbitFiberProduct_symm hreg hn₀ b _).trans
    (h.coe_orbitFiberProductDiffeomorphShiftingLevel_symm hreg b q)

/-- The map `Ψ⁻¹(0) → μ⁻¹(c) ⧸ G_c`, `(x, g G_c) ↦ [g⁻¹ • x]`, is a smooth submersion: it is the
orbit projection of the orbit fibre product read through the identification of points. -/
private theorem isSubmersion_orbitFiberProductProj_comp_levelDiffeomorph :
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    letI := h.orbitFiberProductChartedSpace c hreg b
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    IsSubmersion 𝓘(ℝ, Fin n₀ → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)) ∞
      (h.orbitFiberProductProj c b ∘ h.levelDiffeomorphOrbitFiberProduct hreg hn₀ b) := by
  let _ := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  have := (h.prod_neg_coadjointOrbitForm c).isManifold_levelSubMulAction
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  let _ := h.orbitFiberProductChartedSpace c hreg b
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  exact (h.isSubmersion_orbitFiberProductProj hreg hn d b).comp_diffeomorph
    (h.levelDiffeomorphOrbitFiberProduct hreg hn₀ b) (by simp)

omit [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- The fibres of `(x, g G_c) ↦ [g⁻¹ • x]` on the zero level of the shifting moment map are the
orbits of the coadjoint stabilizer `G_0`, which is all of `G`. -/
private theorem orbitFiberProductProj_levelDiffeomorph_eq_iff
    (p p' : (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) :
    h.orbitFiberProductProj c b (h.levelDiffeomorphOrbitFiberProduct hreg hn₀ b p) =
        h.orbitFiberProductProj c b (h.levelDiffeomorphOrbitFiberProduct hreg hn₀ b p') ↔
      ∃ k : (Lie.coadjointRepresentation ℝ I G).stabilizer 0, k • p' = p := by
  rw [h.orbitFiberProductProj_eq_orbitFiberProductProj_iff, coe_levelDiffeomorphOrbitFiberProduct,
    coe_levelDiffeomorphOrbitFiberProduct]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨⟨k⁻¹, Representation.mem_stabilizer.2 (map_zero _)⟩, Subtype.ext ?_⟩
    rw [SubMulAction.val_smul, Subgroup.smul_def]
    exact inv_smul_eq_iff.2 hk.symm
  · rintro ⟨k, rfl⟩
    exact ⟨(k : G)⁻¹, by rw [SubMulAction.val_smul, Subgroup.smul_def, inv_smul_smul]⟩

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
  -- `(x, g G_c) ↦ [g⁻¹ • x]` is a surjective submersion out of `Ψ⁻¹(0)` whose fibres are the
  -- `G_0`-orbits.
  (h.prod_neg_coadjointOrbitForm c).diffeomorphOfOrbitSubmersion 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
    (h.orbitFiberProductProj c _ ∘
      h.levelDiffeomorphOrbitFiberProduct hreg hn₀ (Module.finBasis ℝ (GroupLieAlgebra I G)))
    (h.isSubmersion_orbitFiberProductProj_comp_levelDiffeomorph hreg hn d hn₀ _)
    ((h.orbitFiberProductProj_surjective _).comp
      (h.levelDiffeomorphOrbitFiberProduct hreg hn₀ _).surjective)
    (h.orbitFiberProductProj_levelDiffeomorph_eq_iff hreg hn₀ _)

/-- **The shifting diffeomorphism on a point of the zero level**: `Φ [p] = q_W (j p)`, where `j`
identifies `Ψ⁻¹(0)` with the orbit fibre product `W_O`, read in any basis `b` of `𝔤`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelDiffeomorphOrbitFiberProduct`), and
`q_W (x, g G_c) = [g⁻¹ • x]` is the orbit projection of the orbit fibre product. -/
theorem shiftingReducedSpaceDiffeomorph_quotientMk
    (p : (h.prod_neg_coadjointOrbitForm c).levelSubMulAction 0) :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    letI := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
    letI := h.orbitFiberProductChartedSpace c hreg b
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    h.shiftingReducedSpaceDiffeomorph c hreg hn d hn₀ d₀ (Quotient.mk _ p) =
      h.orbitFiberProductProj c b (h.levelDiffeomorphOrbitFiberProduct hreg hn₀ b p) := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
  let _ := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  let _ := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
  let _ := h.orbitFiberProductChartedSpace c hreg b
  let _ := h.orbitFiberProductChartedSpace c hreg (Module.finBasis ℝ (GroupLieAlgebra I G))
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  -- By definition `Φ` is induced by `q_W ∘ j` in the basis `Module.finBasis`, and in every basis
  -- `q_W (j p)` is `[g⁻¹ • x]` for `p = (x, g G_c)`.
  refine (congrFun ((h.prod_neg_coadjointOrbitForm c).diffeomorphOfOrbitSubmersion_comp_mk
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀ _
    (h.isSubmersion_orbitFiberProductProj_comp_levelDiffeomorph hreg hn d hn₀ _)
    ((h.orbitFiberProductProj_surjective _).comp
      (h.levelDiffeomorphOrbitFiberProduct hreg hn₀ _).surjective)
    (h.orbitFiberProductProj_levelDiffeomorph_eq_iff hreg hn₀
      (Module.finBasis ℝ (GroupLieAlgebra I G)))) p).trans ?_
  have hfin := h.coe_levelDiffeomorphOrbitFiberProduct hreg hn₀
    (Module.finBasis ℝ (GroupLieAlgebra I G)) p
  have hb := h.coe_levelDiffeomorphOrbitFiberProduct hreg hn₀ b p
  rw [Function.comp_apply,
    h.orbitFiberProductProj_eq _ _ ((QuotientGroup.out_eq' _).trans (congrArg Prod.snd hfin).symm),
    h.orbitFiberProductProj_eq _ _ ((QuotientGroup.out_eq' _).trans (congrArg Prod.snd hb).symm)]
  exact congrArg _ (Subtype.ext (congrArg (fun y ↦ (p.val.2.out)⁻¹ • y.1) (hfin.trans hb.symm)))

/-- **The shifting diffeomorphism on the zero level**: `Φ ∘ π₀ = q_W ∘ j`, where `π₀` is the orbit
projection of `Ψ⁻¹(0)`, `j` identifies `Ψ⁻¹(0)` with the orbit fibre product `W_O`, read in any
basis `b` of `𝔤` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelDiffeomorphOrbitFiberProduct`),
and `q_W (x, g G_c) = [g⁻¹ • x]` is the orbit projection of the orbit fibre product. -/
theorem shiftingReducedSpaceDiffeomorph_comp_quotientMk :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    letI := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
    letI := h.orbitFiberProductChartedSpace c hreg b
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    ⇑(h.shiftingReducedSpaceDiffeomorph c hreg hn d hn₀ d₀) ∘ Quotient.mk _ =
      h.orbitFiberProductProj c b ∘ h.levelDiffeomorphOrbitFiberProduct hreg hn₀ b :=
  funext (h.shiftingReducedSpaceDiffeomorph_quotientMk hreg hn d hn₀ d₀ b)

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
        (h.mem_levelSubMulAction_prod_neg_coadjointOrbitForm.1 hx))⟩ := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := h.isCancelSMul_levelSubMulAction_prod_neg_coadjointOrbitForm (c := c)
  let _ := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  let _ := (h.prod_neg_coadjointOrbitForm c).orbitRelQuotientChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀ d₀
  let _ := h.orbitFiberProductChartedSpace c hreg (Module.finBasis ℝ (GroupLieAlgebra I G))
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  rw [h.shiftingReducedSpaceDiffeomorph_quotientMk hreg hn d hn₀ d₀
      (Module.finBasis ℝ (GroupLieAlgebra I G)),
    h.orbitFiberProductProj_eq _ _
      (congrArg Prod.snd (h.coe_levelDiffeomorphOrbitFiberProduct hreg hn₀ _ ⟨_, hx⟩)).symm]
  exact congrArg _ (Subtype.ext (by simp))

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
  -- `Φ [(z, G_c)] = [1⁻¹ • z] = [z]` (`shiftingReducedSpaceDiffeomorph_mk`).
  refine Eq.trans ?_ ((h.shiftingReducedSpaceDiffeomorph c hreg hn d hn₀ d₀).symm_apply_apply _)
  rw [shiftingReducedSpaceDiffeomorph_mk]
  exact congrArg _ (congrArg _ (Subtype.ext (by simp)))

omit [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- Read on the zero level of the shifting moment map, the form `pr_M^* σ - pr_O^* ω_KKS` of the
orbit fibre product is the restriction of the product form `σ ⊞ (-ω_KKS)`. -/
private theorem mpullback_levelDiffeomorphOrbitFiberProduct_sub :
    letI := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    haveI := (h.prod_neg_coadjointOrbitForm c).isManifold_levelSubMulAction
      (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
    letI := h.orbitFiberProductChartedSpace c hreg b
    haveI := h.isManifold_orbitFiberProduct hreg b
    SmoothForm.mpullback (h.levelDiffeomorphOrbitFiberProduct hreg hn₀ b)
        (h.levelDiffeomorphOrbitFiberProduct hreg hn₀ b).contMDiff
        (SmoothForm.mpullback
            (fun p : OrbitFiberProduct μ c b ↦ p.val.1)
            (contMDiff_fst.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff) σ -
          SmoothForm.mpullback
            (fun p : OrbitFiberProduct μ c b ↦ p.val.2)
            (contMDiff_snd.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff)
            c.coadjointOrbitForm) =
      SmoothForm.mpullback Subtype.val
        ((h.prod_neg_coadjointOrbitForm c).isSmoothEmbedding_coe_levelSubMulAction
          (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀).contMDiff
        (σ.prod (-c.coadjointOrbitForm)) := by
  let _ := (h.prod_neg_coadjointOrbitForm c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  have := (h.prod_neg_coadjointOrbitForm c).isManifold_levelSubMulAction
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀
  let _ := h.orbitFiberProductChartedSpace c hreg b
  have := h.isManifold_orbitFiberProduct hreg b
  have hi₀ := ((h.prod_neg_coadjointOrbitForm c).isSmoothEmbedding_coe_levelSubMulAction
    (h.forall_differential_surjective_prod_neg_coadjointOrbitForm hreg) hn₀).contMDiff
  have hi := (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff
  set j := h.levelDiffeomorphOrbitFiberProduct hreg hn₀ b
  -- The identification `j` is the identity of points, so `pr_M ∘ j` and `pr_O ∘ j` are the two
  -- projections of `M × O` restricted to the zero level.
  rw [LinearMap.map_sub, SmoothForm.mpullback_mpullback_of_comp_eq
      (g := fun p : OrbitFiberProduct μ c b ↦ p.val.1)
      (g' := Prod.fst) j.contMDiff (contMDiff_fst.comp hi) hi₀ contMDiff_fst
      (funext fun p ↦ congrArg Prod.fst (h.coe_levelDiffeomorphOrbitFiberProduct hreg hn₀ b p)),
    SmoothForm.mpullback_mpullback_of_comp_eq
      (g := fun p : OrbitFiberProduct μ c b ↦ p.val.2)
      (g' := Prod.snd) j.contMDiff (contMDiff_snd.comp hi) hi₀ contMDiff_snd
      (funext fun p ↦ congrArg Prod.snd (h.coe_levelDiffeomorphOrbitFiberProduct hreg hn₀ b p)),
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
  set j := h.levelDiffeomorphOrbitFiberProduct hreg hn₀ b
  -- `Φ ∘ π₀ = q_W ∘ j`, where `j` identifies `Ψ⁻¹(0)` with the orbit fibre product, on which the
  -- reduced form of `M` pulls back to `pr_M^* σ - pr_O^* ω_KKS`.
  have hk : ⇑(h.shiftingReducedSpaceDiffeomorph c hreg hn d hn₀ d₀) ∘ Quotient.mk _ =
      h.orbitFiberProductProj c b ∘ j :=
    h.shiftingReducedSpaceDiffeomorph_comp_quotientMk hreg hn d hn₀ d₀ b
  have hqW :=
    (h.mpullback_quotientMk_eq_iff_mpullback_orbitFiberProductProj_eq_sub hreg hn d b hG η).1 hη
  -- Pullback along the surjective submersion `π₀` is injective.
  refine SmoothForm.mpullback_injective_of_surjective hπ₀.contMDiff Quotient.mk_surjective
    (hπ₀.surjective_mfderiv (by simp)) ?_
  rw [hη₀, SmoothForm.mpullback_mpullback_of_comp_eq hπ₀.contMDiff
    (h.shiftingReducedSpaceDiffeomorph c hreg hn d hn₀ d₀).contMDiff j.contMDiff hq.contMDiff hk,
    hqW]
  exact h.mpullback_levelDiffeomorphOrbitFiberProduct_sub hreg hn₀ b

end Reduced

end TauCeti.SmoothTwoForm.IsEquivariantMomentMap
