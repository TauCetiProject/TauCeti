/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.BalancedProduct
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.OrbitFiberProduct

import TauCeti.Geometry.Manifold.Submersion.Split

/-!
# Orbit reduction on the orbit fibre product and the shifting construction

Let a Lie group `G` act smoothly by symplectomorphisms on `(M, σ)`, with coadjoint-equivariant
moment map `μ : M → 𝔤*`, let `c` be a regular value of `μ`, and let `O = G ⧸ G_c` be the coadjoint
orbit of `c`, with its Kirillov–Kostant–Souriau form `ω_KKS` and orbit map `ι_O [g] = Ad*_g c`.
The orbit fibre product

`W_O = {(x, o) ∈ M × O | μ(x) = ι_O(o)}`

(`TauCeti.OrbitFiberProduct`) is an embedded submanifold of `M × O` parametrizing `μ⁻¹(O)`. This
file carries the orbit-reduction identity from the balanced product `Y_O = G ×_{G_c} μ⁻¹(c)` over
to `W_O`, through the diffeomorphism `Φ : Y_O → W_O`, `[g, z] ↦ (g • z, g G_c)`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductDiffeomorph`).

The **orbit projection** of `W_O` onto the reduced space `Q = μ⁻¹(c) ⧸ G_c` is

`q_W : W_O → Q`, `q_W (x, g G_c) = [g⁻¹ • x]`

(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductProj`). It does not depend on the
representative `g` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductProj_eq`):
replacing `g` by `g h` with `h ∈ G_c` moves `g⁻¹ • x` inside its `G_c`-orbit. It satisfies
`q_W ∘ Φ = q_Y` for the projection `q_Y [g, z] = [z]` of the balanced product
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductProj_orbitFiberProductDiffeomorph`),
so it is a smooth surjective submersion, and its fibres are the orbits of the diagonal action
`k • (x, o) = (k • x, k • o)` of `G`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductProj_eq_orbitFiberProductProj_iff`).

When `G` acts properly, preserving `σ`, and `G_c` acts freely on the level, every reduced form
`π^* ω_red = i^* σ` on `Q` satisfies

`q_W^* ω_red = pr_M^* σ - pr_O^* ω_KKS` on `W_O`

(`mpullback_orbitFiberProductProj_eq_sub`, in the namespace
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap`), where `pr_M` and `pr_O` are the two projections of
`W_O ⊆ M × O`. This is the form `ω - μ^* ω_KKS` of orbit reduction on `μ⁻¹(O)`, read on the
manifold `W_O`. Pulled back along `Φ`, the two sides become the two sides of the orbit-reduction
identity `q_Y^* ω_red = i_Y^* σ - pr_Y^* ω_KKS` on `Y_O`
(`mpullback_orbitProj_eq_sub`), and pullback along a diffeomorphism is injective. For a symplectic
`σ`, the Marsden–Weinstein–Meyer reduced form is therefore the unique symplectic form with this
identity (`existsUnique_isSymplectic_mpullback_orbitFiberProductProj_eq_sub`), since pullback along
the surjective submersion `q_W` is injective. Consequently `pr_M^* σ - pr_O^* ω_KKS` is a closed
two-form on `W_O` whose null space at each point is the kernel of the differential of `q_W`
(`isClosed_and_ker_bilinFormAt_sub_eq_ker_mfderiv_orbitFiberProductProj`): its null spaces are
the tangent spaces of the fibres of `q_W`, which are the `G`-orbits of `W_O`.

**The shifting map.** The points of `W_O` are the zeros of the shifting map
`Ψ(x, o) = μ(x) - ι_O(o)` on `M × O`, the moment map of the diagonal action on `M × O⁻`, where `O⁻`
carries `-ω_KKS`. The comparison of `W_O` with the zero level of `Ψ`, and of its reduced form with
the reduced form of `M × O⁻` at zero, is in
`TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.OrbitFiberProduct.Shifting`.

## Main definitions

* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductProj`: the orbit projection
  `q_W : W_O → μ⁻¹(c) ⧸ G_c`, `(x, g G_c) ↦ [g⁻¹ • x]`.

## Main results

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`.

* `orbitFiberProductProj_orbitFiberProductDiffeomorph`: `q_W ∘ Φ = q_Y`.
* `orbitFiberProductProj_eq_orbitFiberProductProj_iff`: the fibres of `q_W` are the `G`-orbits.
* `isSubmersion_orbitFiberProductProj`: `q_W` is a smooth submersion.
* `existsUnique_isSymplectic_mpullback_orbitFiberProductProj_eq_sub`: the reduced form is the
  unique symplectic form with `q_W^* ω_red = pr_M^* σ - pr_O^* ω_KKS`.
* `mpullback_orbitFiberProductProj_eq_sub`: every reduced form `π^* ω_red = i^* σ` of a
  `G`-invariant `σ` satisfies `q_W^* ω_red = pr_M^* σ - pr_O^* ω_KKS`.
* `isClosed_and_ker_bilinFormAt_sub_eq_ker_mfderiv_orbitFiberProductProj`: the form
  `pr_M^* σ - pr_O^* ω_KKS` on `W_O` is closed with null spaces `ker d q_W`.

## References

* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 6.1 (orbit reduction and the shifting theorem).
* E. Meinrenken, *Symplectic geometry*, lecture notes, University of Toronto, 2000,
  Proposition 8.6 (the shifting trick).
* L. Bates, E. Lerman, *Proper group actions and symplectic stratified spaces*, Pacific Journal of
  Mathematics 181 (1997), 201–229, Proposition 11 (the form `ω - μ^* ω_KKS` on `μ⁻¹(O)`).
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
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [FiniteDimensional ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {c : Module.Dual ℝ (GroupLieAlgebra I G)} {κ : Type*}

namespace SmoothTwoForm

namespace IsEquivariantMomentMap

/-! ### The orbit projection -/

section Proj

variable (h : σ.IsEquivariantMomentMap μ) (b : Basis κ ℝ (GroupLieAlgebra I G))

/-- For a point `(x, g G_c)` of the orbit fibre product, `g⁻¹ • x` lies in the level `μ⁻¹(c)`. -/
theorem inv_smul_mem_levelSubMulAction (p : OrbitFiberProduct μ c b) {g : G}
    (hg : (g : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) = p.val.2) :
    g⁻¹ • p.val.1 ∈ h.levelSubMulAction c :=
  h.mem_levelSubMulAction.2 ((h.components_eq_orbitMap_iff b).1 (hg ▸ p.property))

variable (c) in
/-- **The orbit projection of the orbit fibre product** `q_W : W_O → μ⁻¹(c) ⧸ G_c`,
`(x, g G_c) ↦ [g⁻¹ • x]`, for any representative `g`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductProj_eq`). Composed with the
diffeomorphism `G ×_{G_c} μ⁻¹(c) ≃ W_O` it is the projection `[g, z] ↦ [z]`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductProj_orbitFiberProductDiffeomorph`),
and its fibres are the orbits of the diagonal action of `G`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductProj_eq_orbitFiberProductProj_iff`).
-/
def orbitFiberProductProj (p : OrbitFiberProduct μ c b) :
    MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
      (h.levelSubMulAction c) :=
  Quotient.mk _ ⟨_, h.inv_smul_mem_levelSubMulAction b p (QuotientGroup.out_eq' p.val.2)⟩

/-- **The orbit projection in a representative**: `q_W (x, g G_c) = [g⁻¹ • x]` for every `g`
representing the second component. -/
theorem orbitFiberProductProj_eq (p : OrbitFiberProduct μ c b) {g : G}
    (hg : (g : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) = p.val.2) :
    h.orbitFiberProductProj c b p =
      Quotient.mk _ ⟨_, h.inv_smul_mem_levelSubMulAction b p hg⟩ := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul _ g
  rw [hg] at hk
  -- `p.2.out = g k`, so `(p.2.out)⁻¹ • x = k⁻¹ • g⁻¹ • x`.
  refine Quotient.sound ⟨k⁻¹, Subtype.ext ?_⟩
  simp [hk, Subgroup.smul_def, mul_smul]

/-- **The orbit projection on an explicit point**: `q_W (x, g G_c) = [g⁻¹ • x]`. -/
@[simp]
theorem orbitFiberProductProj_mk (x : M) (g : G)
    (hp : ((x, (g : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)) :
      M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) ∈
        {p | (fun i ↦ μ p.1 (b i)) =
          fun i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 (b i)}) :
    h.orbitFiberProductProj c b ⟨(x, g), hp⟩ =
      Quotient.mk _ ⟨g⁻¹ • x, h.inv_smul_mem_levelSubMulAction b ⟨(x, g), hp⟩ rfl⟩ :=
  h.orbitFiberProductProj_eq b _ rfl

/-- For `z` in the level `μ⁻¹(c)`, the point `(z, G_c)` lies in the orbit fibre product. -/
theorem components_eq_orbitMap_one (z : h.levelSubMulAction c) :
    (fun i ↦ μ (z : M) (b i)) = fun i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c
      ((1 : G) : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) (b i) :=
  (h.components_eq_orbitMap_iff b).2 (by simpa using h.mem_levelSubMulAction.1 z.property)

/-- The orbit projection sends the point `(z, G_c)` of the orbit fibre product to the orbit of
`z`, for `z` in the level `μ⁻¹(c)`. -/
theorem orbitFiberProductProj_mk_one (z : h.levelSubMulAction c) :
    h.orbitFiberProductProj c b ⟨((z : M), ((1 : G) : G ⧸
      (Lie.coadjointRepresentation ℝ I G).stabilizer c)), h.components_eq_orbitMap_one b z⟩ =
      Quotient.mk _ z := by
  rw [h.orbitFiberProductProj_eq b _ rfl]
  exact congrArg _ (Subtype.ext (by simp))

/-- The orbit projection is surjective: `q_W (z, G_c) = [z]` for `z` in the level. -/
theorem orbitFiberProductProj_surjective : Surjective (h.orbitFiberProductProj c b) := by
  rintro ⟨z⟩
  exact ⟨_, h.orbitFiberProductProj_mk_one b z⟩

/-- **The fibres of the orbit projection are the `G`-orbits.** Two points of the orbit fibre
product have the same image in `μ⁻¹(c) ⧸ G_c` exactly when they lie in the same orbit of the
diagonal action `k • (x, o) = (k • x, k • o)` of `G` on `M × G ⧸ G_c`. -/
theorem orbitFiberProductProj_eq_orbitFiberProductProj_iff {p p' : OrbitFiberProduct μ c b} :
    h.orbitFiberProductProj c b p = h.orbitFiberProductProj c b p' ↔
      ∃ k : G, k • p.val = p'.val := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective p.val.2
  obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective p'.val.2
  rw [h.orbitFiberProductProj_eq b p hg, h.orbitFiberProductProj_eq b p' hg']
  constructor
  · intro hq
    -- `k • g'⁻¹ • x' = g⁻¹ • x` for some `k ∈ G_c`, so `g' k⁻¹ g⁻¹` moves `(x, g G_c)` to
    -- `(x', g' G_c)`.
    obtain ⟨k, hk⟩ := Quotient.exact hq
    have hk' : (k : G) • g'⁻¹ • p'.val.1 = g⁻¹ • p.val.1 := congrArg Subtype.val hk
    refine ⟨g' * (k : G)⁻¹ * g⁻¹, Prod.ext ?_ ?_⟩
    · simp [mul_smul, ← hk']
    · simp [← hg, ← hg', mul_assoc]
  · rintro ⟨k, hk⟩
    -- `k g G_c = g' G_c`, so `g' = k g h` for some `h ∈ G_c`, and `g'⁻¹ • x' = h⁻¹ • g⁻¹ • x`.
    have hx : k • p.val.1 = p'.val.1 := congrArg Prod.fst hk
    have ho : k • p.val.2 = p'.val.2 := congrArg Prod.snd hk
    rw [← hg, ← hg', MulAction.Quotient.smul_mk, QuotientGroup.eq] at ho
    refine Quotient.sound ⟨⟨_, ho⟩, Subtype.ext ?_⟩
    simp [Subgroup.smul_def, ← hx, mul_smul]

end Proj

/-! ### Comparison with the balanced product -/

section BalancedProduct

variable [Fintype κ] [I.Boundaryless] [I'.Boundaryless] [T2Space M]
  (h : σ.IsEquivariantMomentMap μ) {n : ℕ}
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)
  (b : Basis κ ℝ (GroupLieAlgebra I G))

/-- The diffeomorphism `Φ : G ×_{G_c} μ⁻¹(c) ≃ W_O` is `[g, z] ↦ (g • z, g G_c)` on every point,
read as the map `TauCeti.BalancedProduct.liftProjRightTranslation` into `M × G ⧸ G_c`. -/
theorem coe_orbitFiberProductDiffeomorph
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
    (h.orbitFiberProductDiffeomorph hreg hn d b y :
        M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) =
      BalancedProduct.liftProjRightTranslation (h.levelSubMulActionSubtype c) y := by
  let _ := d.chartedSpace
  have := d.lieGroup
  have := d.contMDiffSMul (M := G) (I'' := I)
  let _ := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  have := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
    (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
  let _ := h.orbitFiberProductChartedSpace c hreg b
  induction y using BalancedProduct.induction_on_toRightTranslation with
  | h g z =>
    rw [h.coe_orbitFiberProductDiffeomorph_mk, BalancedProduct.liftProjRightTranslation_mk,
      coe_levelSubMulActionSubtype]

/-- **`q_W ∘ Φ = q_Y`.** The orbit projection of the orbit fibre product, composed with the
diffeomorphism `Φ : G ×_{G_c} μ⁻¹(c) ≃ W_O`, is the projection `[g, z] ↦ [z]` of the balanced
product onto `μ⁻¹(c) ⧸ G_c`. -/
@[simp]
theorem orbitFiberProductProj_orbitFiberProductDiffeomorph
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
    h.orbitFiberProductProj c b (h.orbitFiberProductDiffeomorph hreg hn d b y) =
      BalancedProduct.orbitProj y := by
  let _ := d.chartedSpace
  have := d.lieGroup
  have := d.contMDiffSMul (M := G) (I'' := I)
  let _ := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  have := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
    (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
  let _ := h.orbitFiberProductChartedSpace c hreg b
  induction y using BalancedProduct.induction_on_toRightTranslation with
  | h g z =>
    have hΦ := h.coe_orbitFiberProductDiffeomorph_mk hreg hn d b g z
    rw [h.orbitFiberProductProj_eq b _ (g := g) (by rw [hΦ]), BalancedProduct.orbitProj_mk]
    exact congrArg _ (Subtype.ext (by simp [hΦ]))

end BalancedProduct

/-! ### The reduced form on the orbit fibre product -/

section Reduced

variable [Fintype κ] [I.Boundaryless] [I'.Boundaryless] [ProperSMul G M]
  (h : σ.IsEquivariantMomentMap μ) {n : ℕ}
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
  (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)
  (b : Basis κ ℝ (GroupLieAlgebra I G))

/-- **The orbit projection of the orbit fibre product is a smooth submersion**
`q_W : W_O → μ⁻¹(c) ⧸ G_c`, for the transverse fibre-product atlas of `W_O` and the atlas of the
quotient manifold theorem on the reduced space, when `G` acts properly and `G_c` acts freely on the
regular level `μ⁻¹(c)`. -/
theorem isSubmersion_orbitFiberProductProj :
    letI := h.orbitFiberProductChartedSpace c hreg b
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    IsSubmersion 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ)
      𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)) ∞ (h.orbitFiberProductProj c b) := by
  let _ := d.chartedSpace
  have := d.lieGroup
  have := d.contMDiffSMul (M := G) (I'' := I)
  let _ := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  have := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
    (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  let _ := BalancedProduct.rightTranslationChartedSpace
    ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c) I
    𝓘(ℝ, Fin n → ℝ) F
  have := BalancedProduct.isManifold_rightTranslation
    (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := h.levelSubMulAction c)
    (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ)) (F := F)
  let _ := h.orbitFiberProductChartedSpace c hreg b
  have := h.isManifold_orbitFiberProduct hreg b
  have hq := BalancedProduct.isSubmersion_orbitProj_rightTranslation (I := I) (F := F)
    (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d)
  -- `q_W = q_Y ∘ Φ⁻¹` is a submersion precomposed with a diffeomorphism.
  set Φ := h.orbitFiberProductDiffeomorph hreg hn d b
  have hqΦ : h.orbitFiberProductProj c b = BalancedProduct.orbitProj ∘ Φ.symm :=
    funext fun p ↦ by
      rw [Function.comp_apply,
        ← h.orbitFiberProductProj_orbitFiberProductDiffeomorph hreg hn d b (Φ.symm p),
        Φ.apply_symm_apply]
  rw [hqΦ]
  exact hq.comp_diffeomorph Φ.symm (by simp)

/-- **The orbit-reduction identity on the orbit fibre product.** Let `G` act smoothly and properly
on `M`, preserving `σ`, with coadjoint-equivariant moment map `μ`, let `c` be a regular value of
`μ`, and let the coadjoint stabilizer `G_c`, with the Lie group structure `d`, act freely on the
level `μ⁻¹(c)`. Every two-form `ω_red` on `Q = μ⁻¹(c) ⧸ G_c` with `π^* ω_red = i^* σ`, for the
orbit projection `π` and the inclusion `i` of the level, satisfies

`q_W^* ω_red = pr_M^* σ - pr_O^* ω_KKS`

on the orbit fibre product `W_O = {(x, o) ∈ M × O | μ(x) = ι_O(o)}`, for the orbit projection
`q_W (x, g G_c) = [g⁻¹ • x]`, the two projections `pr_M (x, o) = x` and `pr_O (x, o) = o`, and the
Kirillov–Kostant–Souriau form `ω_KKS` on `O = G ⧸ G_c`. Neither closedness nor nondegeneracy of
`σ` is needed. -/
theorem mpullback_orbitFiberProductProj_eq_sub
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
          SmoothForm.mpullback (fun p : OrbitFiberProduct μ c b ↦ p.val.1)
              (contMDiff_fst.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff) σ -
            SmoothForm.mpullback (fun p : OrbitFiberProduct μ c b ↦ p.val.2)
              (contMDiff_snd.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff)
              c.coadjointOrbitForm := by
  intro η hη
  let _ := d.chartedSpace
  have := d.lieGroup
  have := d.contMDiffSMul (M := G) (I'' := I)
  let _ := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  have := h.contMDiffSMul_levelSubMulAction d.contMDiff_subtypeVal
    (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn)
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  let _ := BalancedProduct.rightTranslationChartedSpace
    ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c) I
    𝓘(ℝ, Fin n → ℝ) F
  have := BalancedProduct.isManifold_rightTranslation
    (K := (Lie.coadjointRepresentation ℝ I G).stabilizer c) (Z := h.levelSubMulAction c)
    (I := I) (IZ := 𝓘(ℝ, Fin n → ℝ)) (F := F)
  let _ := h.orbitFiberProductChartedSpace c hreg b
  have := h.isManifold_orbitFiberProduct hreg b
  set Φ := h.orbitFiberProductDiffeomorph hreg hn d b
  -- Pulled back along `Φ`, `q_W`, `pr_M` and `pr_O` become `q_Y`, `i_Y` and `pr_Y`, and the
  -- identity becomes the orbit-reduction identity on the balanced product.
  have hq : h.orbitFiberProductProj c b ∘ Φ = BalancedProduct.orbitProj :=
    funext (h.orbitFiberProductProj_orbitFiberProductDiffeomorph hreg hn d b)
  have hM : (fun p : OrbitFiberProduct μ c b ↦ p.val.1) ∘ Φ =
      BalancedProduct.liftRightTranslation (h.levelSubMulActionSubtype c) :=
    funext fun y ↦ by
      rw [Function.comp_apply, h.coe_orbitFiberProductDiffeomorph hreg hn d b y,
        BalancedProduct.fst_liftProjRightTranslation]
  have hO : (fun p : OrbitFiberProduct μ c b ↦ p.val.2) ∘ Φ =
      BalancedProduct.proj (h.levelSubMulAction c) Subgroup.RightTranslation.quotientMk_smul :=
    funext fun y ↦ by
      rw [Function.comp_apply, h.coe_orbitFiberProductDiffeomorph hreg hn d b y,
        BalancedProduct.snd_liftProjRightTranslation]
  refine SmoothForm.mpullback_injective_of_rightInverse (F := ℝ) (k := 2) Φ.contMDiff
    Φ.symm.contMDiff Φ.apply_symm_apply ?_
  rw [map_sub, SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_mpullback]
  simp only [hq, hM, hO]
  exact h.mpullback_orbitProj_eq_sub (F := F) hG (h.contMDiff_levelSubMulActionSubtype hreg hn)
    (fun z ↦ by simpa using h.mem_levelSubMulAction.1 z.property)
    (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff
    (by simpa only [coe_levelSubMulActionSubtype] using hη)

/-- **The Marsden–Weinstein–Meyer reduced form on the orbit fibre product.** Let a Lie group `G`
act smoothly and properly by symplectomorphisms on a symplectic manifold `(M, σ)`, with
coadjoint-equivariant moment map `μ`, let `c` be a regular value of `μ`, and let the coadjoint
stabilizer `G_c`, with the Lie group structure `d`, act freely on the level `μ⁻¹(c)`. Then the
reduced space `Q = μ⁻¹(c) ⧸ G_c` carries a unique symplectic form `ω_red` with

`q_W^* ω_red = pr_M^* σ - pr_O^* ω_KKS`

on the orbit fibre product `W_O = {(x, o) ∈ M × O | μ(x) = ι_O(o)}`, for the orbit projection
`q_W (x, g G_c) = [g⁻¹ • x]` and the two projections `pr_M (x, o) = x` and `pr_O (x, o) = o`, with
the Kirillov–Kostant–Souriau form `ω_KKS` on `O = G ⧸ G_c`. It is the reduced form
`π^* ω_red = i^* σ` of `existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback`. -/
theorem existsUnique_isSymplectic_mpullback_orbitFiberProductProj_eq_sub (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    letI := h.orbitFiberProductChartedSpace c hreg b
    haveI := h.isManifold_orbitFiberProduct hreg b
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    ∃! η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c)),
      η.IsSymplectic ∧
        SmoothForm.mpullback (h.orbitFiberProductProj c b)
            (h.isSubmersion_orbitFiberProductProj hreg hn d b).contMDiff η =
          SmoothForm.mpullback (fun p : OrbitFiberProduct μ c b ↦ p.val.1)
              (contMDiff_fst.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff) σ -
            SmoothForm.mpullback (fun p : OrbitFiberProduct μ c b ↦ p.val.2)
              (contMDiff_snd.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff)
              c.coadjointOrbitForm := by
  let _ := h.levelSubMulActionChartedSpace c hreg hn
  have := h.isManifold_levelSubMulAction hreg hn
  let _ := h.orbitFiberProductChartedSpace c hreg b
  have := h.isManifold_orbitFiberProduct hreg b
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  have hq := h.isSubmersion_orbitFiberProductProj hreg hn d b
  -- The reduced form satisfies the identity, and pullback along the surjective submersion `q_W` is
  -- injective.
  obtain ⟨η, ⟨hησ, hη⟩, -⟩ :=
    h.existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback hreg hn d hσ hG
  have hηq := h.mpullback_orbitFiberProductProj_eq_sub hreg hn d b hG η hη
  exact ⟨η, ⟨hησ, hηq⟩, fun η' hη' ↦ SmoothForm.mpullback_injective_of_surjective hq.contMDiff
    (h.orbitFiberProductProj_surjective b) (hq.surjective_mfderiv (by simp)) (hη'.2.trans hηq.symm)⟩

/-- **The null foliation of `pr_M^* σ - pr_O^* ω_KKS` on the orbit fibre product.** With the
hypotheses of the Marsden–Weinstein–Meyer theorem, the two-form `pr_M^* σ - pr_O^* ω_KKS` on
`W_O = {(x, o) ∈ M × O | μ(x) = ι_O(o)}` is closed, and its null space at each point is the kernel
of the differential of the orbit projection `q_W : W_O → μ⁻¹(c) ⧸ G_c`. So the null distribution
of this form is `ker d q_W`, the tangent distribution to the fibres of `q_W`, which are the
`G`-orbits of `W_O`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductProj_eq_orbitFiberProductProj_iff`).
-/
theorem isClosed_and_ker_bilinFormAt_sub_eq_ker_mfderiv_orbitFiberProductProj
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    letI := h.orbitFiberProductChartedSpace c hreg b
    haveI := h.isManifold_orbitFiberProduct hreg b
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    (SmoothForm.mpullback (fun p : OrbitFiberProduct μ c b ↦ p.val.1)
          (contMDiff_fst.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff) σ -
        SmoothForm.mpullback (fun p : OrbitFiberProduct μ c b ↦ p.val.2)
          (contMDiff_snd.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff)
          c.coadjointOrbitForm).IsClosed ∧
      ∀ p, LinearMap.ker ((SmoothForm.mpullback (fun p : OrbitFiberProduct μ c b ↦ p.val.1)
          (contMDiff_fst.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff) σ -
        SmoothForm.mpullback (fun p : OrbitFiberProduct μ c b ↦ p.val.2)
          (contMDiff_snd.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff)
          c.coadjointOrbitForm).bilinFormAt p) =
        (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
            (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
              finrank ℝ (κ → ℝ)) → ℝ)
          𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
          (h.orbitFiberProductProj c b) p).ker := by
  let _ := h.orbitFiberProductChartedSpace c hreg b
  have := h.isManifold_orbitFiberProduct hreg b
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  have hq := h.isSubmersion_orbitFiberProductProj hreg hn d b
  -- A symplectic form on the base of a surjective submersion pulls back to a closed form whose
  -- null spaces are the vertical directions.
  obtain ⟨η, ⟨hη, hηq⟩, -⟩ :=
    h.existsUnique_isSymplectic_mpullback_orbitFiberProductProj_eq_sub hreg hn d b hσ hG
  exact (isSymplectic_iff_of_mpullback_eq hq.contMDiff (h.orbitFiberProductProj_surjective b)
    (hq.surjective_mfderiv (by simp)) hηq).1 hη

end Reduced

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
