/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Prod
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.OrbitFiberProduct.Quotient

import TauCeti.Geometry.Manifold.Diffeomorph.Subtype
import TauCeti.Geometry.Manifold.Submersion.Diffeomorph
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Shifting
import TauCeti.Topology.Algebra.ProperAction.Basic

/-!
# The shifting trick

Let a Lie group `G` act smoothly and properly by symplectomorphisms on `(M, σ)`, with
coadjoint-equivariant moment map `μ : M → 𝔤*`, let `c` be a regular value of `μ`, and let
`O = G ⧸ G_c` be the coadjoint orbit of `c`, with its Kirillov–Kostant–Souriau form `ω_KKS` and
orbit map `ι_O [g] = Ad*_g c`. Write `O⁻` for the orbit with the opposite form `-ω_KKS`. The
diagonal action of `G` on `M × O⁻` is Hamiltonian, with the **shifting moment map**

`Ψ(x, o) = μ(x) - ι_O(o)`

(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.sub_orbitMap`), a coadjoint-equivariant moment map
of the product form `σ ⊞ (-ω_KKS)`. The **shifting trick** says that reduction of `M` at `c` is
reduction of `M × O⁻` at zero. This file proves it for the Marsden–Weinstein–Meyer reduced spaces
of `TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace`:

* zero is a regular value of `Ψ`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.forall_differential_surjective_sub_orbitMap`),
  since `dμ` alone is onto along `μ⁻¹(O)`;
* the stabilizer `G_0 = G` of zero acts freely on the level `Ψ⁻¹(0)` when `G_c` acts freely on
  `μ⁻¹(c)`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isCancelSMul_levelSubMulAction_sub_orbitMap`);
* the reduced spaces are diffeomorphic,

  `Ψ⁻¹(0) ⧸ G ≃ μ⁻¹(c) ⧸ G_c`, `[(x, g G_c)] ↦ [g⁻¹ • x]`, with inverse `[z] ↦ [(z, G_c)]`

  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitRelQuotientSubOrbitMapDiffeomorph`), for
  the atlases of the quotient manifold theorem on both sides, built from any embedded Lie subgroup
  structures on `G_c` and on `G_0`;
* this diffeomorphism pulls the reduced form of `M` at `c` back to the reduced form of `M × O⁻` at
  zero (`IsEquivariantMomentMap.mpullback_orbitRelQuotientSubOrbitMapDiffeomorph`).

So for a `G`-invariant symplectic form `σ`, the two reduced symplectic manifolds of the
Marsden–Weinstein–Meyer theorem are symplectomorphic.

The level `Ψ⁻¹(0)` consists of the same points as the orbit fibre product
`W_O = {(x, o) | μ(x) = ι_O(o)}` (`TauCeti.OrbitFiberProduct`), and both atlases make the inclusion
into `M × O` a smooth embedding, so the identity of points is a diffeomorphism
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductDiffeomorphLevelSubMulAction`).
Through it, the diffeomorphism above is induced by the orbit projection
`q_W (x, g G_c) = [g⁻¹ • x]`, a surjective submersion whose fibres are the `G`-orbits
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductProj_eq_orbitFiberProductProj_iff`).
On `W_O` the restriction of `σ ⊞ (-ω_KKS)` is `pr_M^* σ - pr_O^* ω_KKS`, which is
`q_W^* ω_red` for every reduced form `ω_red` of `M` at `c`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback_orbitFiberProductProj_eq_sub`); for a
symplectic `σ`, `ω_red` is the unique symplectic form with this identity read on `Ψ⁻¹(0)`
(`existsUnique_isSymplectic_mpullback_orbitFiberProductProj_comp_symm_eq_sub`).

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`.

* `sub_orbitMap`: `Ψ` is a coadjoint-equivariant moment map of `σ ⊞ (-ω_KKS)`.
* `isRegularValue_sub_orbitMap`: zero is a regular value of `Ψ`, read in a basis of `𝔤`.
* `forall_differential_surjective_sub_orbitMap`: zero is a regular value of `Ψ`.
* `isCancelSMul_levelSubMulAction_sub_orbitMap`: `G_0` acts freely on `Ψ⁻¹(0)`.
* `orbitFiberProductDiffeomorphLevelSubMulAction`: the identity of points `W_O ≃ Ψ⁻¹(0)` as a
  diffeomorphism of the fibre-product atlas and the regular-level atlas.
* `existsUnique_isSymplectic_mpullback_orbitFiberProductProj_comp_symm_eq_sub`: the reduced form
  is the unique symplectic form with `q_O^* ω_red = pr_M^* σ - pr_O^* ω_KKS` on `Ψ⁻¹(0)`.
* `orbitRelQuotientSubOrbitMapDiffeomorph`: the diffeomorphism `Ψ⁻¹(0) ⧸ G_0 ≃ μ⁻¹(c) ⧸ G_c`, with
  the formulas `orbitRelQuotientSubOrbitMapDiffeomorph_mk` and
  `orbitRelQuotientSubOrbitMapDiffeomorph_symm_mk`.
* `mpullback_orbitRelQuotientSubOrbitMapDiffeomorph`: it pulls the reduced form at `c` back to the
  reduced form at zero.

## References

* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26 (the shifting trick).
* E. Meinrenken, *Symplectic geometry*, lecture notes, University of Toronto, 2000,
  Proposition 8.6 (the shifting trick).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 24.4 (reduction at other levels).
-/

public section

noncomputable section

open Module
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

/-! ### The shifting moment map -/

include h in
variable (c) in
/-- **The shifting moment map.** The diagonal action of `G` on `M × O⁻`, for the coadjoint orbit
`O = G ⧸ G_c` with the opposite `-ω_KKS` of its Kirillov–Kostant–Souriau form, has the
coadjoint-equivariant moment map `Ψ(x, o) = μ(x) - ι_O(o)`, for the orbit map
`ι_O [g] = Ad*_g c`. -/
theorem sub_orbitMap :
    (σ.prod (-c.coadjointOrbitForm)).IsEquivariantMomentMap
      fun p : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c ↦
        μ p.1 - (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 := by
  simpa only [sub_eq_add_neg] using h.prod c.isEquivariantMomentMap_coadjointOrbitForm.neg

/-- A point `(x, o)` lies on the level `Ψ⁻¹(0)` of the shifting moment map exactly when
`μ(x) = ι_O(o)`. -/
theorem mem_levelSubMulAction_sub_orbitMap
    {p : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c} :
    p ∈ (h.sub_orbitMap c).levelSubMulAction 0 ↔
      μ p.1 = (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 := by
  rw [mem_levelSubMulAction, sub_eq_zero]

/-- The level `Ψ⁻¹(0)` of the shifting moment map is the orbit fibre product `W_O`, as a set. -/
private theorem mem_levelSubMulAction_sub_orbitMap_iff {κ : Type*}
    (b : Basis κ ℝ (GroupLieAlgebra I G))
    {p : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c} :
    p ∈ (h.sub_orbitMap c).levelSubMulAction 0 ↔
      (fun i ↦ μ p.1 (b i)) = fun i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 (b i) :=
  h.mem_levelSubMulAction_sub_orbitMap.trans (components_eq_orbitMap_iff_apply_eq b).symm

/-- **Zero is a regular value of the shifting map along the coadjoint orbit**
`Ψ(x, o) = μ(x) - ι_O(o)` on `M × G ⧸ G_c`, read in the basis `b`, when `c` is a regular value of
the coadjoint-equivariant moment map `μ`. -/
theorem isRegularValue_sub_orbitMap
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
    {κ : Type*} [Fintype κ] (b : Basis κ ℝ (GroupLieAlgebra I G)) :
    IsRegularValue (I'.prod
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)))
      𝓘(ℝ, κ → ℝ)
      (fun p : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c ↦
        fun i ↦ μ p.1 (b i) - (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 (b i)) 0 :=
  h.isRegularValue_sub hreg b
    (fun o ↦ (c.contMDiff_orbitMap_coadjointRepresentation_components b o).mdifferentiableAt
      (by simp))
    fun o ↦ ⟨o.out, by rw [← Representation.orbitMap_mk, QuotientGroup.out_eq']⟩

/-- **Zero is a regular value of the shifting moment map** `Ψ(x, o) = μ(x) - ι_O(o)` when `c` is a
regular value of `μ`: at every point of `Ψ⁻¹(0)` the differential of `Ψ` is onto `𝔤*`. Indeed
`dμ` alone is onto there, by equivariance. -/
theorem forall_differential_surjective_sub_orbitMap
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x)) :
    ∀ p, μ p.1 - (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 = 0 →
      Function.Surjective ((h.sub_orbitMap c).differential p) := by
  intro p hp
  set b := Module.finBasis ℝ (GroupLieAlgebra I G)
  refine ((h.sub_orbitMap c).toIsMomentMap.isRegularPoint_components_iff b).1 ?_
  have hp' : (fun i ↦ μ p.1 (b i) - (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 (b i)) =
      0 := by
    funext i
    rw [Pi.zero_apply, ← LinearMap.sub_apply, hp, LinearMap.zero_apply]
  simpa only [LinearMap.sub_apply] using
    isRegularValue_iff.1 (h.isRegularValue_sub_orbitMap hreg b) p hp'

variable [FiniteDimensional ℝ E']

/-- **The stabilizer of zero acts freely on the level of the shifting moment map** when the
coadjoint stabilizer `G_c` acts freely on the level `μ⁻¹(c)`: the stabilizer of zero is all of
`G`, and `G` acts freely on the orbit fibre product
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isCancelSMul_orbitFiberProduct`). -/
theorem isCancelSMul_levelSubMulAction_sub_orbitMap
    [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] :
    IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer 0)
      ((h.sub_orbitMap c).levelSubMulAction 0) := by
  set b := Module.finBasis ℝ (GroupLieAlgebra I G)
  let _ := h.orbitFiberProductMulAction c b
  have := h.isCancelSMul_orbitFiberProduct (c := c) b
  refine isCancelSMul_iff_stabilizer_eq_bot.2 fun z ↦ ?_
  rw [stabilizer_levelSubMulAction_eq_bot_iff]
  refine (Subgroup.eq_bot_iff_forall _).2 fun k hk ↦ ?_
  exact IsCancelSMul.eq_one_of_smul (P := OrbitFiberProduct μ c b)
    (x := ⟨z.val, (h.mem_levelSubMulAction_sub_orbitMap_iff b).1 z.property⟩)
    (Subtype.ext ((h.coe_smul_orbitFiberProduct b k _).trans (MulAction.mem_stabilizer_iff.1 hk)))

/-! ### The orbit projection on the level of the shifting moment map -/

/-- The orbit projection `(x, g G_c) ↦ [g⁻¹ • x]` of the orbit fibre product, read on the level
`Ψ⁻¹(0)` of the shifting moment map, which consists of the same points. -/
private def levelProj (z : (h.sub_orbitMap c).levelSubMulAction 0) :
    MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
      (h.levelSubMulAction c) :=
  h.orbitFiberProductProj c (Module.finBasis ℝ (GroupLieAlgebra I G))
    ⟨z.val, (h.mem_levelSubMulAction_sub_orbitMap_iff _).1 z.property⟩

/-- Two points of the level `Ψ⁻¹(0)` have the same image under the orbit projection exactly when
they lie in the same orbit of the stabilizer `G_0 = G` of zero. -/
private theorem levelProj_eq_levelProj_iff (z z' : (h.sub_orbitMap c).levelSubMulAction 0) :
    h.levelProj z = h.levelProj z' ↔
      ∃ k : (Lie.coadjointRepresentation ℝ I G).stabilizer 0, k • z' = z := by
  have hstab (k : G) : k ∈ (Lie.coadjointRepresentation ℝ I G).stabilizer 0 := by
    rw [Representation.stabilizer_zero]
    exact Subgroup.mem_top k
  -- The fibres of the orbit projection are the `G`-orbits, and the stabilizer of zero is `G`.
  rw [levelProj, levelProj, h.orbitFiberProductProj_eq_orbitFiberProductProj_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨⟨k⁻¹, hstab _⟩, Subtype.ext (by
      rw [SubMulAction.val_smul, Subgroup.mk_smul, ← hk, inv_smul_smul])⟩
  · rintro ⟨k, rfl⟩
    exact ⟨(k : G)⁻¹, by rw [SubMulAction.val_smul, Subgroup.smul_def, inv_smul_smul]⟩

/-- For `z` in the level `μ⁻¹(c)`, the point `(z, G_c)` lies on the level `Ψ⁻¹(0)`. -/
theorem mk_one_mem_levelSubMulAction_sub_orbitMap (z : h.levelSubMulAction c) :
    ((z : M), ((1 : G) : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)) ∈
      (h.sub_orbitMap c).levelSubMulAction 0 :=
  (h.mem_levelSubMulAction_sub_orbitMap_iff (Module.finBasis ℝ (GroupLieAlgebra I G))).2
    (h.components_eq_orbitMap_one _ z)

/-- A point `z` of the level `μ⁻¹(c)` gives the point `(z, G_c)` of the level `Ψ⁻¹(0)`. -/
private def levelMk (z : h.levelSubMulAction c) : (h.sub_orbitMap c).levelSubMulAction 0 :=
  ⟨_, h.mk_one_mem_levelSubMulAction_sub_orbitMap z⟩

/-- The orbit projection sends `(z, G_c)` to the orbit of `z`. -/
private theorem levelProj_levelMk (z : h.levelSubMulAction c) :
    h.levelProj (h.levelMk z) = Quotient.mk _ z :=
  h.orbitFiberProductProj_mk_one _ z

/-! ### The level of the shifting moment map as a manifold -/

section Level

variable [I'.Boundaryless] {κ : Type*} [Fintype κ]
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  (b : Basis κ ℝ (GroupLieAlgebra I G)) {n₀ : ℕ}
  (hn₀ : finrank ℝ
      (E' × Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
    finrank ℝ (GroupLieAlgebra I G) = n₀)

/-- **The orbit fibre product is the zero level of the shifting moment map.** The pairs `(x, o)`
of `M × G ⧸ G_c` with `μ(x) = ι_O(o)` are the points of the level `Ψ⁻¹(0)` of the shifting moment
map `Ψ(x, o) = μ(x) - ι_O(o)`, and the identity of these points is a diffeomorphism from the
transverse fibre-product atlas of `W_O`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductChartedSpace`), read in the basis
`b`, to the regular-level atlas of `Ψ⁻¹(0)` of the Marsden–Weinstein–Meyer theorem
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelSubMulActionChartedSpace`). -/
def orbitFiberProductDiffeomorphLevelSubMulAction :
    letI := h.orbitFiberProductChartedSpace c hreg b
    letI := (h.sub_orbitMap c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
    OrbitFiberProduct μ c b ≃ₘ⟮𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ), 𝓘(ℝ, Fin n₀ → ℝ)⟯
      (h.sub_orbitMap c).levelSubMulAction 0 :=
  letI := h.orbitFiberProductChartedSpace c hreg b
  letI := (h.sub_orbitMap c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
  -- Both atlases make the inclusion into `M × G ⧸ G_c` a smooth embedding, so the identity of
  -- `M × G ⧸ G_c` restricts to a diffeomorphism between them.
  (Diffeomorph.refl _ (M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)
    ∞).subtypeOfIsSmoothEmbedding
    (s := {p | (fun i ↦ μ p.1 (b i)) =
      fun i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 (b i)})
    (t := (h.sub_orbitMap c).levelSubMulAction 0)
    (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b)
    ((h.sub_orbitMap c).isSmoothEmbedding_coe_levelSubMulAction
      (h.forall_differential_surjective_sub_orbitMap hreg) hn₀)
    fun _ ↦ (h.mem_levelSubMulAction_sub_orbitMap_iff b).symm

/-- The identification of the orbit fibre product with the level `Ψ⁻¹(0)` is the identity on
points. -/
@[simp]
theorem coe_orbitFiberProductDiffeomorphLevelSubMulAction (p : OrbitFiberProduct μ c b) :
    letI := h.orbitFiberProductChartedSpace c hreg b
    letI := (h.sub_orbitMap c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
    (h.orbitFiberProductDiffeomorphLevelSubMulAction hreg b hn₀ p :
        M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) = p.val := by
  let _ := h.orbitFiberProductChartedSpace c hreg b
  let _ := (h.sub_orbitMap c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
  exact Diffeomorph.subtypeOfIsSmoothEmbedding_apply_coe ..

/-- The inverse identification of the level `Ψ⁻¹(0)` with the orbit fibre product is the identity
on points. -/
@[simp]
theorem coe_orbitFiberProductDiffeomorphLevelSubMulAction_symm
    (z : (h.sub_orbitMap c).levelSubMulAction 0) :
    letI := h.orbitFiberProductChartedSpace c hreg b
    letI := (h.sub_orbitMap c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
    (((h.orbitFiberProductDiffeomorphLevelSubMulAction hreg b hn₀).symm z :
        OrbitFiberProduct μ c b) : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) =
      z.val := by
  let _ := h.orbitFiberProductChartedSpace c hreg b
  let _ := (h.sub_orbitMap c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
  exact Diffeomorph.subtypeOfIsSmoothEmbedding_symm_apply_coe ..

end Level

/-! ### The reduced spaces -/

section Quotient

variable [I'.Boundaryless] [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x)) {n n₀ : ℕ}
  (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
  (hn₀ : finrank ℝ
      (E' × Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
    finrank ℝ (GroupLieAlgebra I G) = n₀)
  {F F₀ : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [FiniteDimensional ℝ F₀]
  (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)
  (d₀ : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer 0) F₀)

omit [ProperSMul G M]
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
  [FiniteDimensional ℝ F₀] in
/-- The orbit projection on the level `Ψ⁻¹(0)` is the orbit projection of the orbit fibre product
after the identification of the two levels. -/
private theorem levelProj_eq_comp :
    letI := (h.sub_orbitMap c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
    letI := h.orbitFiberProductChartedSpace c hreg (Module.finBasis ℝ (GroupLieAlgebra I G))
    h.levelProj = h.orbitFiberProductProj c (Module.finBasis ℝ (GroupLieAlgebra I G)) ∘
      (h.orbitFiberProductDiffeomorphLevelSubMulAction hreg
        (Module.finBasis ℝ (GroupLieAlgebra I G)) hn₀).symm :=
  funext fun z ↦ by
    rw [Function.comp_apply, levelProj]
    exact congrArg _ (Subtype.ext (h.coe_orbitFiberProductDiffeomorphLevelSubMulAction_symm
      hreg (Module.finBasis ℝ (GroupLieAlgebra I G)) hn₀ z).symm)

/-- The orbit projection on the level `Ψ⁻¹(0)` is a smooth submersion onto the reduced space
`μ⁻¹(c) ⧸ G_c`. -/
private theorem isSubmersion_levelProj :
    letI := (h.sub_orbitMap c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    Manifold.IsSubmersion 𝓘(ℝ, Fin n₀ → ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)) ∞
      (h.levelProj (c := c)) := by
  set b := Module.finBasis ℝ (GroupLieAlgebra I G)
  let _ := (h.sub_orbitMap c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
  have := (h.sub_orbitMap c).isManifold_levelSubMulAction
    (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
  let _ := h.orbitFiberProductChartedSpace c hreg b
  have := h.isManifold_orbitFiberProduct hreg b
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  set φ := (h.orbitFiberProductDiffeomorphLevelSubMulAction hreg b hn₀).symm
  have hq := h.isSubmersion_orbitFiberProductProj hreg hn d b
  rw [h.levelProj_eq_comp hreg hn₀]
  exact hq.comp_diffeomorph φ (by simp)

/-- **The reduced form on the zero level of the shifting moment map.** With the hypotheses of the
Marsden–Weinstein–Meyer theorem, give the level `Ψ⁻¹(0)` of the shifting moment map
`Ψ(x, o) = μ(x) - ι_O(o)` on `M × O`, `O = G ⧸ G_c`, its regular-level atlas, and let
`q_O : Ψ⁻¹(0) → μ⁻¹(c) ⧸ G_c`, `(x, g G_c) ↦ [g⁻¹ • x]`, be the orbit projection
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductProj` read through the identification
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductDiffeomorphLevelSubMulAction` of
`Ψ⁻¹(0)` with the orbit fibre product. Then the reduced space carries a unique symplectic form
`ω_red` with

`q_O^* ω_red = pr_M^* σ - pr_O^* ω_KKS`

on `Ψ⁻¹(0)`, for the two projections `pr_M (x, o) = x` and `pr_O (x, o) = o`. This is the form of
`M × O⁻`, with the reversed Kirillov–Kostant–Souriau form, restricted to the zero level of its
moment map `Ψ`: the shifting construction. -/
theorem existsUnique_isSymplectic_mpullback_orbitFiberProductProj_comp_symm_eq_sub {κ : Type*}
    [Fintype κ] (b : Basis κ ℝ (GroupLieAlgebra I G)) (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    letI := h.orbitFiberProductChartedSpace c hreg b
    haveI := h.isManifold_orbitFiberProduct hreg b
    letI := (h.sub_orbitMap c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
    haveI := (h.sub_orbitMap c).isManifold_levelSubMulAction
      (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    ∃! η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c)),
      η.IsSymplectic ∧
        SmoothForm.mpullback
            (h.orbitFiberProductProj c b ∘
              (h.orbitFiberProductDiffeomorphLevelSubMulAction hreg b hn₀).symm)
            ((h.isSubmersion_orbitFiberProductProj hreg hn d b).contMDiff.comp
              (h.orbitFiberProductDiffeomorphLevelSubMulAction hreg b hn₀).symm.contMDiff) η =
          SmoothForm.mpullback
              (fun p : (h.sub_orbitMap c).levelSubMulAction 0 ↦ p.val.1)
              (contMDiff_fst.comp ((h.sub_orbitMap c).isSmoothEmbedding_coe_levelSubMulAction
                (h.forall_differential_surjective_sub_orbitMap hreg) hn₀).contMDiff) σ -
            SmoothForm.mpullback
              (fun p : (h.sub_orbitMap c).levelSubMulAction 0 ↦ p.val.2)
              (contMDiff_snd.comp ((h.sub_orbitMap c).isSmoothEmbedding_coe_levelSubMulAction
                (h.forall_differential_surjective_sub_orbitMap hreg) hn₀).contMDiff)
              c.coadjointOrbitForm := by
  let _ := h.orbitFiberProductChartedSpace c hreg b
  have := h.isManifold_orbitFiberProduct hreg b
  let _ := (h.sub_orbitMap c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
  have := (h.sub_orbitMap c).isManifold_levelSubMulAction
    (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  set e := h.orbitFiberProductDiffeomorphLevelSubMulAction hreg b hn₀
  -- Pulled back along `e`, the three maps become `q_W`, `pr_M` and `pr_O` on the orbit fibre
  -- product, and pullback along the diffeomorphism `e` is injective.
  have he := SmoothForm.mpullback_injective_of_rightInverse (F := ℝ) (k := 2) e.contMDiff
    e.symm.contMDiff e.apply_symm_apply
  refine (existsUnique_congr fun η ↦ and_congr_right fun _ ↦ ?_).1
    (h.existsUnique_isSymplectic_mpullback_orbitFiberProductProj_eq_sub hreg hn d b hσ hG)
  rw [← he.eq_iff, map_sub, SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_mpullback]
  have hq : (h.orbitFiberProductProj c b ∘ e.symm) ∘ e = h.orbitFiberProductProj c b :=
    funext fun p ↦ by simp
  have hM : (fun p : (h.sub_orbitMap c).levelSubMulAction 0 ↦ p.val.1) ∘ e = fun p ↦ p.val.1 :=
    funext fun p ↦ congrArg Prod.fst
      (h.coe_orbitFiberProductDiffeomorphLevelSubMulAction hreg b hn₀ p)
  have hO : (fun p : (h.sub_orbitMap c).levelSubMulAction 0 ↦ p.val.2) ∘ e = fun p ↦ p.val.2 :=
    funext fun p ↦ congrArg Prod.snd
      (h.coe_orbitFiberProductDiffeomorphLevelSubMulAction hreg b hn₀ p)
  simp only [hq, hM, hO]

/-- On the orbit fibre product, `q_W^* η` is the restriction of `σ ⊞ (-ω_KKS)` for every reduced
form `η` of `M` at `c`. -/
private theorem mpullback_orbitFiberProductProj_eq_prod {κ : Type*} [Fintype κ]
    (b : Basis κ ℝ (GroupLieAlgebra I G))
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    haveI := h.isManifold_levelSubMulAction hreg hn
    letI := h.orbitFiberProductChartedSpace c hreg b
    haveI := h.isManifold_orbitFiberProduct hreg b
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    ∀ η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c)),
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff σ →
        SmoothForm.mpullback (h.orbitFiberProductProj c b)
            (h.isSubmersion_orbitFiberProductProj hreg hn d b).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff
            (σ.prod (-c.coadjointOrbitForm)) := by
  intro η hη
  let _ := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let _ := h.orbitFiberProductChartedSpace c hreg b
  have := h.isManifold_orbitFiberProduct hreg b
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  rw [h.mpullback_orbitFiberProductProj_eq_sub hreg hn d b hG η hη, prod_def, map_add,
    SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback, map_neg, sub_eq_add_neg]
  -- The two sides differ only in writing `Prod.fst ∘ Subtype.val` for `fun p ↦ p.val.1` (and
  -- likewise for `snd`), which agree by unfolding `Function.comp`, and in the smoothness proofs
  -- passed to `mpullback`, which agree by proof irrelevance.
  rfl

/-- **The shifting trick: reduction of `M` at `c` is reduction of `M × O⁻` at zero.** Let a Lie
group `G` act smoothly and properly on `M` with coadjoint-equivariant moment map `μ`, let `c` be a
regular value of `μ`, and let the coadjoint stabilizer `G_c` act freely on the level `μ⁻¹(c)`.
Then the Marsden–Weinstein–Meyer reduced space `Ψ⁻¹(0) ⧸ G_0` of `M × G ⧸ G_c` for the shifting
moment map `Ψ(x, o) = μ(x) - ι_O(o)` is diffeomorphic to the reduced space `μ⁻¹(c) ⧸ G_c` of `M`,
by

`[(x, g G_c)] ↦ [g⁻¹ • x]`

(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitRelQuotientSubOrbitMapDiffeomorph_mk`), with
inverse `[z] ↦ [(z, G_c)]`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitRelQuotientSubOrbitMapDiffeomorph_symm_mk`).
Both reduced spaces carry the atlases of the quotient manifold theorem, for any embedded Lie
subgroup structures `d` on `G_c` and `d₀` on the stabilizer `G_0 = G` of zero; the hypotheses of the
reduction theorem at zero follow from those at `c`. -/
def orbitRelQuotientSubOrbitMapDiffeomorph :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_sub_orbitMap (c := c)
    letI := (h.sub_orbitMap c).orbitRelQuotientChartedSpace 0
      (h.forall_differential_surjective_sub_orbitMap hreg) hn₀ d₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer 0)
        ((h.sub_orbitMap c).levelSubMulAction 0) ≃ₘ⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace F₀ (Fin n₀ → ℝ)),
      𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))⟯
      MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c) :=
  haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  haveI := h.isCancelSMul_levelSubMulAction_sub_orbitMap (c := c)
  have hreg₀ := h.forall_differential_surjective_sub_orbitMap hreg
  letI := (h.sub_orbitMap c).levelSubMulActionChartedSpace 0 hreg₀ hn₀
  letI := (h.sub_orbitMap c).orbitRelQuotientChartedSpace 0 hreg₀ hn₀ d₀
  letI := h.orbitRelQuotientChartedSpace c hreg hn d
  -- The orbit projection descends to the quotient by its fibres, the `G_0`-orbits; smoothness in
  -- both directions descends along the surjective submersions `π₀` and `q_O`.
  let e : MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer 0)
      ((h.sub_orbitMap c).levelSubMulAction 0) ≃
      MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c) :=
    Equiv.trans
      (Quotient.congrRight fun z z' ↦
        (MulAction.orbitRel_apply.trans MulAction.mem_orbit_iff).trans
          (h.levelProj_eq_levelProj_iff z z').symm)
      (Setoid.quotientKerEquivOfSurjective h.levelProj fun y ↦
        Quotient.inductionOn y fun z ↦ ⟨_, h.levelProj_levelMk z⟩)
  e.diffeomorphOfSubmersions
    ((h.sub_orbitMap c).isSubmersion_quotientMk_levelSubMulAction hreg₀ hn₀ d₀)
    Quotient.mk_surjective (h.isSubmersion_levelProj hreg hn hn₀ d) (funext fun _ ↦ rfl)

/-- The shifting diffeomorphism sends the orbit of a point of `Ψ⁻¹(0)` to its orbit projection. -/
private theorem orbitRelQuotientSubOrbitMapDiffeomorph_quotientMk
    (z : (h.sub_orbitMap c).levelSubMulAction 0) :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_sub_orbitMap (c := c)
    letI := (h.sub_orbitMap c).orbitRelQuotientChartedSpace 0
      (h.forall_differential_surjective_sub_orbitMap hreg) hn₀ d₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    h.orbitRelQuotientSubOrbitMapDiffeomorph hreg hn hn₀ d d₀ (Quotient.mk _ z) =
      h.levelProj z := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := h.isCancelSMul_levelSubMulAction_sub_orbitMap (c := c)
  let _ := (h.sub_orbitMap c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
  let _ := (h.sub_orbitMap c).orbitRelQuotientChartedSpace 0
    (h.forall_differential_surjective_sub_orbitMap hreg) hn₀ d₀
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  -- `Quotient.congrRight` and `Setoid.quotientKerEquivOfSurjective` compute on `Quotient.mk` by
  -- `Quot.lift_beta`, so the underlying equivalence sends `[z]` to `q_O z` definitionally.
  exact Equiv.diffeomorphOfSubmersions_apply _ _ _ _ _ _

/-- **The formula for the shifting diffeomorphism**: the orbit of `(x, g G_c)` is sent to the
orbit of `g⁻¹ • x`. -/
@[simp]
theorem orbitRelQuotientSubOrbitMapDiffeomorph_mk (x : M) (g : G)
    (hp : ((x, (g : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)) :
      M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) ∈
        (h.sub_orbitMap c).levelSubMulAction 0) :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_sub_orbitMap (c := c)
    letI := (h.sub_orbitMap c).orbitRelQuotientChartedSpace 0
      (h.forall_differential_surjective_sub_orbitMap hreg) hn₀ d₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    h.orbitRelQuotientSubOrbitMapDiffeomorph hreg hn hn₀ d d₀ (Quotient.mk _ ⟨(x, g), hp⟩) =
      Quotient.mk _ ⟨g⁻¹ • x, h.mem_levelSubMulAction.2
        (h.apply_eq_orbitMap_iff.1 (h.mem_levelSubMulAction_sub_orbitMap.1 hp))⟩ :=
  (h.orbitRelQuotientSubOrbitMapDiffeomorph_quotientMk hreg hn hn₀ d d₀ _).trans
    (h.orbitFiberProductProj_mk _ x g _)

/-- **The inverse of the shifting diffeomorphism** sends the orbit of a point `z` of the level
`μ⁻¹(c)` to the orbit of `(z, G_c)`. -/
@[simp]
theorem orbitRelQuotientSubOrbitMapDiffeomorph_symm_mk (z : h.levelSubMulAction c) :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_sub_orbitMap (c := c)
    letI := (h.sub_orbitMap c).orbitRelQuotientChartedSpace 0
      (h.forall_differential_surjective_sub_orbitMap hreg) hn₀ d₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    (h.orbitRelQuotientSubOrbitMapDiffeomorph hreg hn hn₀ d d₀).symm (Quotient.mk _ z) =
      Quotient.mk _ ⟨((z : M), ((1 : G) : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)),
        h.mk_one_mem_levelSubMulAction_sub_orbitMap z⟩ := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := h.isCancelSMul_levelSubMulAction_sub_orbitMap (c := c)
  let _ := (h.sub_orbitMap c).orbitRelQuotientChartedSpace 0
    (h.forall_differential_surjective_sub_orbitMap hreg) hn₀ d₀
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  exact (Equiv.symm_apply_eq (h.orbitRelQuotientSubOrbitMapDiffeomorph hreg hn hn₀ d d₀).toEquiv).2
    ((h.levelProj_levelMk z).symm.trans
      (h.orbitRelQuotientSubOrbitMapDiffeomorph_quotientMk hreg hn hn₀ d d₀ _).symm)

/-- **The shifting trick for the reduced forms.** With the hypotheses of
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitRelQuotientSubOrbitMapDiffeomorph`, let `G`
preserve `σ`. Let `η` be a reduced form of `M` at `c`, with `π^* η = i^* σ` for the orbit
projection `π` and the inclusion `i` of the level `μ⁻¹(c)`, and let `η₀` be a reduced form of
`M × O⁻` at zero, with `π₀^* η₀ = i₀^* (σ ⊞ (-ω_KKS))` for the orbit projection `π₀` and the
inclusion `i₀` of the level `Ψ⁻¹(0)`. Then the shifting diffeomorphism
`Ψ⁻¹(0) ⧸ G_0 ≃ μ⁻¹(c) ⧸ G_c` pulls `η` back to `η₀`. For a symplectic `σ`, `η` and `η₀` are the
reduced symplectic forms of the Marsden–Weinstein–Meyer theorem
(`IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback`),
so the two reduced spaces are symplectomorphic. -/
theorem mpullback_orbitRelQuotientSubOrbitMapDiffeomorph
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
    haveI := h.isCancelSMul_levelSubMulAction_sub_orbitMap (c := c)
    letI := (h.sub_orbitMap c).levelSubMulActionChartedSpace 0
      (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := (h.sub_orbitMap c).orbitRelQuotientChartedSpace 0
      (h.forall_differential_surjective_sub_orbitMap hreg) hn₀ d₀
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    haveI := (h.sub_orbitMap c).isManifold_levelSubMulAction
      (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := (h.sub_orbitMap c).isManifold_orbitRelQuotient
      (h.forall_differential_surjective_sub_orbitMap hreg) hn₀ d₀
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    ∀ (η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c)))
      (η₀ : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F₀ (Fin n₀ → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer 0)
          ((h.sub_orbitMap c).levelSubMulAction 0))),
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff σ →
        SmoothForm.mpullback _ ((h.sub_orbitMap c).isSubmersion_quotientMk_levelSubMulAction
            (h.forall_differential_surjective_sub_orbitMap hreg) hn₀ d₀).contMDiff η₀ =
          SmoothForm.mpullback Subtype.val
            ((h.sub_orbitMap c).isSmoothEmbedding_coe_levelSubMulAction
              (h.forall_differential_surjective_sub_orbitMap hreg) hn₀).contMDiff
            (σ.prod (-c.coadjointOrbitForm)) →
        SmoothForm.mpullback (h.orbitRelQuotientSubOrbitMapDiffeomorph hreg hn hn₀ d d₀)
          (h.orbitRelQuotientSubOrbitMapDiffeomorph hreg hn hn₀ d d₀).contMDiff η = η₀ := by
  intro η η₀ hη hη₀
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := h.isCancelSMul_levelSubMulAction_sub_orbitMap (c := c)
  let _ := (h.sub_orbitMap c).levelSubMulActionChartedSpace 0
    (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
  let _ := h.levelSubMulActionChartedSpace c hreg hn
  let _ := h.orbitFiberProductChartedSpace c hreg (Module.finBasis ℝ (GroupLieAlgebra I G))
  let _ := (h.sub_orbitMap c).orbitRelQuotientChartedSpace 0
    (h.forall_differential_surjective_sub_orbitMap hreg) hn₀ d₀
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  have := (h.sub_orbitMap c).isManifold_levelSubMulAction
    (h.forall_differential_surjective_sub_orbitMap hreg) hn₀
  have := h.isManifold_levelSubMulAction hreg hn
  have := h.isManifold_orbitFiberProduct hreg (Module.finBasis ℝ (GroupLieAlgebra I G))
  have := (h.sub_orbitMap c).isManifold_orbitRelQuotient
    (h.forall_differential_surjective_sub_orbitMap hreg) hn₀ d₀
  have := h.isManifold_orbitRelQuotient hreg hn d
  have hsub₀ := (h.sub_orbitMap c).isSubmersion_quotientMk_levelSubMulAction
    (h.forall_differential_surjective_sub_orbitMap hreg) hn₀ d₀
  have hq := h.isSubmersion_orbitFiberProductProj hreg hn d
    (Module.finBasis ℝ (GroupLieAlgebra I G))
  set φ := (h.orbitFiberProductDiffeomorphLevelSubMulAction hreg
    (Module.finBasis ℝ (GroupLieAlgebra I G)) hn₀).symm
  -- Read on `Ψ⁻¹(0)`, the diffeomorphism is `q_W ∘ φ` for the identification `φ` of the level
  -- with the orbit fibre product, on which `q_W^* η` is the restriction of `σ ⊞ (-ω_KKS)`.
  have he : ⇑(h.orbitRelQuotientSubOrbitMapDiffeomorph hreg hn hn₀ d d₀) ∘ Quotient.mk _ =
      h.orbitFiberProductProj c (Module.finBasis ℝ (GroupLieAlgebra I G)) ∘ φ :=
    funext fun z ↦ (h.orbitRelQuotientSubOrbitMapDiffeomorph_quotientMk hreg hn hn₀ d d₀ z).trans
      (congrFun (h.levelProj_eq_comp hreg hn₀) z)
  have hval : Subtype.val ∘ φ = Subtype.val :=
    funext (h.coe_orbitFiberProductDiffeomorphLevelSubMulAction_symm hreg _ hn₀)
  have h₁ := SmoothForm.mpullback_mpullback_of_comp_eq hsub₀.contMDiff
    (h.orbitRelQuotientSubOrbitMapDiffeomorph hreg hn hn₀ d d₀).contMDiff φ.contMDiff
    hq.contMDiff he η
  rw [h.mpullback_orbitFiberProductProj_eq_prod hreg hn d _ hG η hη,
    SmoothForm.mpullback_mpullback φ Subtype.val,
    SmoothForm.mpullback_congr _
      ((h.sub_orbitMap c).isSmoothEmbedding_coe_levelSubMulAction
        (h.forall_differential_surjective_sub_orbitMap hreg) hn₀).contMDiff hval] at h₁
  -- Pullback along the surjective submersion `π₀` is injective.
  refine SmoothForm.mpullback_injective_of_surjective hsub₀.contMDiff Quotient.mk_surjective
    (hsub₀.surjective_mfderiv (by simp)) ?_
  rw [hη₀, h₁]

end Quotient

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
