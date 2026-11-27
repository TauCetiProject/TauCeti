/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Orbit
public import TauCeti.Geometry.Lie.Subgroup.BalancedProduct
public import TauCeti.Geometry.Manifold.FiberProduct.Manifold
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace

import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.RegularLevel

/-!
# The orbit fibre product `W_O` and the balanced product `G ×_{G_c} μ⁻¹(c)`

Let a Lie group `G` act smoothly on a manifold `M` with a coadjoint-equivariant moment map
`μ : M → 𝔤*`, let `c` be a regular value of `μ`, and let `O = G ⧸ G_c` be the coadjoint orbit of
`c` with its homogeneous smooth structure and the injective orbit map `ι_O [g] = Ad*_g c`. The
**orbit fibre product**

`W_O = {(x, o) ∈ M × O | μ(x) = ι_O(o)}`

(`TauCeti.OrbitFiberProduct`, with `μ` and `ι_O` read in a basis `b` of `𝔤`, which does not
change its points: `TauCeti.components_eq_orbitMap_iff_apply_eq`) parametrizes the preimage
`μ⁻¹(O)`, a point `x` with `μ(x) = Ad*_g c` being recorded together with the unique point
`g G_c` of `O` over `μ(x)`. By equivariance `μ` is a submersion at every point over `O`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.differential_surjective_of_apply_eq`), so `μ` and
`ι_O` are transverse and `W_O` is an embedded submanifold of `M × O`, with the atlas of the
transverse fibre-product theorem
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductChartedSpace`).

This file identifies `W_O` with the balanced product `Y_O = G ×_{G_c} μ⁻¹(c)`, the quotient of
`G × μ⁻¹(c)` by `(g, z) ∼ (g h, h⁻¹ • z)` for `h ∈ G_c`, through

`Φ : Y_O → W_O`, `Φ [g, z] = (g • z, g G_c)`

(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductDiffeomorph`). It is a
diffeomorphism with inverse `(x, g G_c) ↦ [g, g⁻¹ • x]`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductDiffeomorph_symm_apply`):
`g⁻¹ • x` lies in the level because `μ(g⁻¹ • x) = Ad*_(g⁻¹) μ(x) = c`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.apply_eq_orbitMap_iff`). The map `Φ` is
equivariant for the action `k • [g, z] = [k g, z]` on `Y_O` and the diagonal action on `M × O`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.coe_orbitFiberProductDiffeomorph_smul`). Its
general form, for any equivariant embedding of a `G_c`-manifold into `M`, is
`TauCeti.BalancedProduct.liftProjDiffeomorphRightTranslation`.

On `Y_O` the reduced form of reduction at `c` satisfies the orbit-reduction identity
`q_Y^* ω_red = i_Y^* σ - pr_Y^* ω_KKS` (`existsUnique_isSymplectic_mpullback_orbitProj_eq_sub`, in
the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`), where `i_Y` and `pr_Y` are the two
components of `Φ`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.coe_orbitFiberProductDiffeomorph_mk`).
`TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.OrbitFiberProduct.ReducedForm` transports this
identity across `Φ` to `W_O` (`existsUnique_isSymplectic_mpullback_orbitFiberProductProj_eq_sub`,
in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`), and
`TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.OrbitFiberProduct.Shifting` identifies `W_O`
with the zero level of the shifting map on `M × O⁻`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductDiffeomorphLevelSubMulAction`).

## Main definitions

* `TauCeti.OrbitFiberProduct`: the orbit fibre product
  `W_O`, as a subtype of `M × G ⧸ G_c`.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductChartedSpace`: its atlas as a
  transverse fibre product.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductDiffeomorph`: the diffeomorphism
  `G ×_{G_c} μ⁻¹(c) ≃ W_O`, `[g, z] ↦ (g • z, g G_c)`.

## References

* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 6.1 (orbit reduction and the shifting theorem).
* J. E. Marsden, G. Misiołek, J.-P. Ortega, M. Perlmutter, T. S. Ratiu, *Hamiltonian Reduction by
  Stages*, Lecture Notes in Mathematics 1913, Springer, 2007, Section 1.2 (orbit reduction
  through `G ×_{G_c} μ⁻¹(c)`).
-/

public section

noncomputable section

open Function Module Manifold
open scoped Manifold ContDiff

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
  Lie.isClosed_stabilizer_coadjointRepresentation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {c : Module.Dual ℝ (GroupLieAlgebra I G)} {κ : Type*}

variable (μ c) in
/-- **The orbit fibre product** `W_O = {(x, o) ∈ M × O | μ(x) = ι_O(o)}` of a moment map `μ` and
the orbit map `ι_O [g] = Ad*_g c` of the coadjoint orbit `O = G ⧸ G_c`, with both maps read in a
basis `b` of `𝔤`. For a coadjoint-equivariant moment map and a regular value `c`, it is a manifold
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductChartedSpace`) diffeomorphic to
`G ×_{G_c} μ⁻¹(c)` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductDiffeomorph`). -/
abbrev OrbitFiberProduct (b : Basis κ ℝ (GroupLieAlgebra I G)) : Type _ :=
  {p : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c //
    (fun i ↦ μ p.1 (b i)) = fun i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 (b i)}

omit [FiniteDimensional ℝ E] [TopologicalSpace M] [MulAction G M] in
/-- A pair `(x, o)` lies in the orbit fibre product exactly when `μ(x) = ι_O(o)`, whatever the
basis `b` used to read `μ` and `ι_O`. -/
theorem components_eq_orbitMap_iff_apply_eq (b : Basis κ ℝ (GroupLieAlgebra I G))
    {p : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c} :
    ((fun i ↦ μ p.1 (b i)) = fun i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 (b i)) ↔
      μ p.1 = (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 :=
  ⟨fun hp ↦ b.ext fun i ↦ congrFun hp i, fun hp ↦ by rw [hp]⟩

namespace SmoothTwoForm

namespace IsEquivariantMomentMap

/-- **The points of `M` over a point of the coadjoint orbit.** For a coadjoint-equivariant moment
map, `μ(x) = Ad*_g c` exactly when `g⁻¹ • x` lies in the level `μ⁻¹(c)`. -/
theorem apply_eq_orbitMap_iff (h : σ.IsEquivariantMomentMap μ) {x : M} {g : G} :
    μ x = (Lie.coadjointRepresentation ℝ I G).orbitMap c
      (g : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) ↔ μ (g⁻¹ • x) = c := by
  rw [Representation.orbitMap_mk, h.apply_smul]
  constructor
  · intro hx
    rw [hx, Representation.inv_self_apply]
  · intro hx
    rw [← hx, Representation.self_inv_apply]

/-- A pair `(x, g G_c)` lies in the orbit fibre product exactly when `g⁻¹ • x` lies in the level
`μ⁻¹(c)`. -/
theorem components_eq_orbitMap_iff (h : σ.IsEquivariantMomentMap μ)
    (b : Basis κ ℝ (GroupLieAlgebra I G)) {x : M} {g : G} :
    ((fun i ↦ μ x (b i)) = fun i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c
      (g : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) (b i)) ↔
      μ (g⁻¹ • x) = c :=
  (components_eq_orbitMap_iff_apply_eq (p := (x, _)) b).trans h.apply_eq_orbitMap_iff

/-- The image of `[g, z] ↦ (g • z, g G_c)` is the orbit fibre product. -/
private theorem range_coe_orbitFiberProduct (h : σ.IsEquivariantMomentMap μ)
    (b : Basis κ ℝ (GroupLieAlgebra I G)) :
    Set.range (Subtype.val : OrbitFiberProduct μ c b → _) =
      Set.range (BalancedProduct.liftProjRightTranslation (h.levelSubMulActionSubtype c)) := by
  ext p
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective p.2
  rw [BalancedProduct.mem_range_liftProjRightTranslation_iff _ hg, coe_levelSubMulActionSubtype,
    Subtype.range_coe_subtype, Subtype.range_coe_subtype, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
    h.mem_levelSubMulAction, ← hg]
  exact h.components_eq_orbitMap_iff b

variable [Fintype κ] [I.Boundaryless]

/-- **The moment map is transverse to the orbit map** when `c` is a regular value and `μ` is
coadjoint-equivariant: at every point `(x, o)` of the orbit fibre product, the ranges of the
differentials of the components of `μ` at `x` and of `ι_O` at `o`, read in the basis `b`, span
`ℝ^κ`. Indeed `dμ_x` alone is surjective, by
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.differential_surjective_of_apply_eq`. This is the
transversality hypothesis of `TauCeti.transverseFiberProductChartedSpace`. -/
theorem range_mfderiv_components_sup_eq_top (h : σ.IsEquivariantMomentMap μ)
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
    (b : Basis κ ℝ (GroupLieAlgebra I G))
    (p : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)
    (hp : (fun i ↦ μ p.1 (b i)) =
      fun i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 (b i)) :
    (mfderiv I' 𝓘(ℝ, κ → ℝ) (fun x i ↦ μ x (b i)) p.1).range ⊔
      (((tangentSpaceCast 𝓘(ℝ, κ → ℝ)
        ((fun o i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c o (b i)) p.2)
        ((fun x i ↦ μ x (b i)) p.1)).toContinuousLinearMap).comp
          (mfderiv
            𝓘(ℝ, Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c))
            𝓘(ℝ, κ → ℝ) (fun o i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c o (b i))
            p.2)).range = ⊤ := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective p.2
  have hx : μ p.1 = Lie.coadjointRepresentation ℝ I G g c := by
    rw [← Representation.orbitMap_mk, hg]
    exact (components_eq_orbitMap_iff_apply_eq b).1 hp
  have hs := isRegularPoint_iff.1 ((h.toIsMomentMap.isRegularPoint_components_iff b).2
    (h.differential_surjective_of_apply_eq hreg hx))
  rw [LinearMap.range_eq_top.2 hs, top_sup_eq]

variable [I'.Boundaryless]

variable (c) in
/-- **The atlas of the orbit fibre product** `W_O`, modelled on `ℝ^(dim M + dim O - dim 𝔤)`: the
atlas of the transverse fibre product `TauCeti.transverseFiberProductChartedSpace` of the
components of `μ` and of the orbit map `ι_O` in the basis `b`. They are transverse because `c` is a
regular value and `μ` is equivariant. -/
@[instance_reducible]
def orbitFiberProductChartedSpace (h : σ.IsEquivariantMomentMap μ)
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
    (b : Basis κ ℝ (GroupLieAlgebra I G)) :
    ChartedSpace (Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ)
      (OrbitFiberProduct μ c b) :=
  transverseFiberProductChartedSpace (by simp) (h.toIsMomentMap.contMDiff_components b)
    (c.contMDiff_orbitMap_coadjointRepresentation_components b)
    (h.range_mfderiv_components_sup_eq_top hreg b)

/-- **The orbit fibre product is a smooth manifold**, for the atlas
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductChartedSpace`. -/
theorem isManifold_orbitFiberProduct (h : σ.IsEquivariantMomentMap μ)
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
    (b : Basis κ ℝ (GroupLieAlgebra I G)) :
    letI := h.orbitFiberProductChartedSpace c hreg b
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ) ∞
      (OrbitFiberProduct μ c b) :=
  isManifold_transverseFiberProduct (by simp) (h.toIsMomentMap.contMDiff_components b)
    (c.contMDiff_orbitMap_coadjointRepresentation_components b)
    (h.range_mfderiv_components_sup_eq_top hreg b)

/-- **The orbit fibre product is an embedded submanifold** of `M × G ⧸ G_c`: its inclusion is a
smooth embedding. -/
theorem isSmoothEmbedding_coe_orbitFiberProduct (h : σ.IsEquivariantMomentMap μ)
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
    (b : Basis κ ℝ (GroupLieAlgebra I G)) :
    letI := h.orbitFiberProductChartedSpace c hreg b
    IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ)
      (I'.prod
        𝓘(ℝ, Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)))
      ∞ (Subtype.val : OrbitFiberProduct μ c b → _) :=
  isSmoothEmbedding_coe_transverseFiberProduct (by simp) (h.toIsMomentMap.contMDiff_components b)
    (c.contMDiff_orbitMap_coadjointRepresentation_components b)
    (h.range_mfderiv_components_sup_eq_top hreg b)

/-! ### The diffeomorphism with the balanced product -/

variable [T2Space M] (h : σ.IsEquivariantMomentMap μ) {n : ℕ}
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)
  (b : Basis κ ℝ (GroupLieAlgebra I G))

/-- **The balanced product `G ×_{G_c} μ⁻¹(c)` is the orbit fibre product `W_O`.** Let a Lie group
`G` act smoothly on a Hausdorff manifold `M` with a coadjoint-equivariant moment map `μ`, let `c`
be a regular value of `μ`, and give the coadjoint stabilizer `G_c` an embedded Lie subgroup
structure `d`. Then

`Φ : G ×_{G_c} μ⁻¹(c) → W_O`, `[g, z] ↦ (g • z, g G_c)`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.coe_orbitFiberProductDiffeomorph_mk`),

is a diffeomorphism with inverse
`(x, g G_c) ↦ [g, g⁻¹ • x]`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductDiffeomorph_symm_apply`), for the
atlas of the balanced product and the transverse fibre-product atlas of `W_O`. -/
def orbitFiberProductDiffeomorph :
    letI := d.chartedSpace
    haveI := d.lieGroup
    haveI := d.contMDiffSMul (M := G) (I'' := I)
    letI := h.levelSubMulActionChartedSpace c hreg hn
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
      (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
    letI := BalancedProduct.rightTranslationChartedSpace
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c) I
      𝓘(ℝ, Fin n → ℝ) F
    letI := h.orbitFiberProductChartedSpace c hreg b
    BalancedProduct ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        ((Lie.coadjointRepresentation ℝ I G).stabilizer c).RightTranslation
        (h.levelSubMulAction c) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (Fin n → ℝ))),
      𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ)⟯
      OrbitFiberProduct μ c b :=
  letI := d.chartedSpace
  haveI := d.lieGroup
  haveI := d.contMDiffSMul (M := G) (I'' := I)
  letI := h.levelSubMulActionChartedSpace c hreg hn
  haveI := h.isManifold_levelSubMulAction hreg hn
  haveI := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
    (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
  letI := h.orbitFiberProductChartedSpace c hreg b
  BalancedProduct.liftProjDiffeomorphRightTranslation (I := I) (F := F)
    (h.levelSubMulActionSubtype c)
    (by rw [coe_levelSubMulActionSubtype]; exact h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
    (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b) (h.range_coe_orbitFiberProduct b)

/-- `Φ` sends `[g, z]` to `(g • z, g G_c)`. -/
@[simp]
theorem coe_orbitFiberProductDiffeomorph_mk (g : G) (z : h.levelSubMulAction c) :
    letI := d.chartedSpace
    haveI := d.lieGroup
    haveI := d.contMDiffSMul (M := G) (I'' := I)
    letI := h.levelSubMulActionChartedSpace c hreg hn
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
      (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
    letI := BalancedProduct.rightTranslationChartedSpace
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c) I
      𝓘(ℝ, Fin n → ℝ) F
    letI := h.orbitFiberProductChartedSpace c hreg b
    (h.orbitFiberProductDiffeomorph hreg hn d b
        (BalancedProduct.mk _ (Subgroup.toRightTranslation _ g) z) :
        M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) =
      (g • (z : M), (g : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)) := by
  let _ := d.chartedSpace
  have := d.lieGroup
  have := d.contMDiffSMul (M := G) (I'' := I)
  let _ := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  have := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
    (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
  let _ := h.orbitFiberProductChartedSpace c hreg b
  rw [orbitFiberProductDiffeomorph,
    BalancedProduct.apply_liftProjDiffeomorphRightTranslation (e := Subtype.val),
    BalancedProduct.liftProjRightTranslation_mk, coe_levelSubMulActionSubtype]

/-- **`Φ` is `G`-equivariant**, for the action `k • [g, z] = [k g, z]` on the balanced product and
the diagonal action `k • (x, o) = (k • x, k • o)` on `M × G ⧸ G_c`. -/
@[simp]
theorem coe_orbitFiberProductDiffeomorph_smul (k : G)
    (y : BalancedProduct ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c).RightTranslation
      (h.levelSubMulAction c)) :
    letI := d.chartedSpace
    haveI := d.lieGroup
    haveI := d.contMDiffSMul (M := G) (I'' := I)
    letI := h.levelSubMulActionChartedSpace c hreg hn
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
      (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
    letI := BalancedProduct.rightTranslationChartedSpace
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c) I
      𝓘(ℝ, Fin n → ℝ) F
    letI := h.orbitFiberProductChartedSpace c hreg b
    (h.orbitFiberProductDiffeomorph hreg hn d b (k • y) :
        M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) =
      k • (h.orbitFiberProductDiffeomorph hreg hn d b y :
        M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) := by
  let _ := d.chartedSpace
  have := d.lieGroup
  have := d.contMDiffSMul (M := G) (I'' := I)
  let _ := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  have := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
    (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
  let _ := h.orbitFiberProductChartedSpace c hreg b
  rw [orbitFiberProductDiffeomorph,
    BalancedProduct.apply_liftProjDiffeomorphRightTranslation (e := Subtype.val),
    BalancedProduct.apply_liftProjDiffeomorphRightTranslation (e := Subtype.val),
    BalancedProduct.liftProjRightTranslation_smul]

/-- **The inverse of `Φ`** sends `(x, g G_c)` to `[g, g⁻¹ • x]`. -/
theorem orbitFiberProductDiffeomorph_symm_apply (p : OrbitFiberProduct μ c b) {g : G}
    (hg : (g : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) = p.val.2) :
    letI := d.chartedSpace
    haveI := d.lieGroup
    haveI := d.contMDiffSMul (M := G) (I'' := I)
    letI := h.levelSubMulActionChartedSpace c hreg hn
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
      (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
    letI := BalancedProduct.rightTranslationChartedSpace
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c) I
      𝓘(ℝ, Fin n → ℝ) F
    letI := h.orbitFiberProductChartedSpace c hreg b
    (h.orbitFiberProductDiffeomorph hreg hn d b).symm p =
      BalancedProduct.mk _ (Subgroup.toRightTranslation _ g)
        (⟨g⁻¹ • p.val.1, h.mem_levelSubMulAction.2
          ((h.components_eq_orbitMap_iff b).1 (hg ▸ p.property))⟩ : h.levelSubMulAction c) := by
  let _ := d.chartedSpace
  have := d.lieGroup
  have := d.contMDiffSMul (M := G) (I'' := I)
  let _ := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  have := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
    (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
  let _ := BalancedProduct.rightTranslationChartedSpace
    ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c) I
    𝓘(ℝ, Fin n → ℝ) F
  let _ := h.orbitFiberProductChartedSpace c hreg b
  refine (h.orbitFiberProductDiffeomorph hreg hn d b).injective (Subtype.ext ?_)
  rw [Diffeomorph.coe_toEquiv, Diffeomorph.apply_symm_apply,
    coe_orbitFiberProductDiffeomorph_mk, smul_inv_smul, hg]

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
