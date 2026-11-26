/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.OrbitFiberProduct.ReducedForm

import TauCeti.Geometry.Manifold.GroupAction.Restrict
import TauCeti.Topology.Algebra.ProperAction.Basic

/-!
# The quotient of the orbit fibre product by `G`

Let a Lie group `G` act smoothly and properly by symplectomorphisms on `(M, σ)`, with
coadjoint-equivariant moment map `μ : M → 𝔤*`, let `c` be a regular value of `μ` whose coadjoint
stabilizer `G_c` acts freely on the level `μ⁻¹(c)`, and let `O = G ⧸ G_c` be the coadjoint orbit of
`c`, with orbit map `ι_O [g] = Ad*_g c`. The orbit fibre product

`W_O = {(x, o) ∈ M × O | μ(x) = ι_O(o)}`

(`TauCeti.OrbitFiberProduct`) is an embedded submanifold of `M × O`. This file shows that the
quotient `W_O ⧸ G` is a smooth manifold of its own, canonically diffeomorphic to the reduced space
`Q = μ⁻¹(c) ⧸ G_c`, and that it carries the reduced symplectic form.

* The diagonal action `k • (x, o) = (k • x, k • o)` of `G` on `M × O` preserves `W_O`, because
  `μ` and `ι_O` are both equivariant
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductMulAction`).
* This action is smooth
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.contMDiffSMul_orbitFiberProduct`), since `W_O` is
  embedded in `M × O`; proper
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.properSMul_orbitFiberProduct`), since a diagonal
  action is proper when it is proper on the first factor; and free
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isCancelSMul_orbitFiberProduct`): if
  `k • (x, g G_c) = (x, g G_c)`, then `g⁻¹ k g` lies in `G_c` and fixes the point `g⁻¹ • x` of the
  level, so it is trivial.
* By the quotient manifold theorem, `W_O ⧸ G` is a smooth manifold and the orbit projection
  `π_W : W_O → W_O ⧸ G` is a submersion. The orbit projection `q_W (x, g G_c) = [g⁻¹ • x]` of
  `W_O` onto `Q` is a surjective submersion whose fibres are the `G`-orbits, so it descends to a
  diffeomorphism

  `e : W_O ⧸ G ≃ Q`, `e [(x, g G_c)] = [g⁻¹ • x]`

  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductQuotientDiffeomorph`), with
  `e ∘ π_W = q_W` and inverse `[z] ↦ [(z, G_c)]`. Composed with the diffeomorphism
  `Φ : G ×_{G_c} μ⁻¹(c) ≃ W_O`, `[g, z] ↦ (g • z, g G_c)`, it gives `e ∘ π_W ∘ Φ = q_Y`, the
  projection `[g, z] ↦ [z]` of the balanced product
  (`orbitFiberProductQuotientDiffeomorph_mk_orbitFiberProductDiffeomorph`).
* Consequently `W_O ⧸ G` carries a unique symplectic form `η` with
  `π_W^* η = pr_M^* σ - pr_O^* ω_KKS` on `W_O`, namely the pullback of the Marsden–Weinstein–Meyer
  reduced form along `e`
  (`existsUnique_isSymplectic_mpullback_quotientMk_orbitFiberProduct_eq_sub`). So the reduced space
  of `M` at `c` is the orbit space of `W_O`, with the form `ω - μ^* ω_KKS` of orbit reduction
  descended to it.

## Main definitions

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`.

* `orbitFiberProductMulAction`: the diagonal action of `G` on `W_O`.
* `orbitFiberProductQuotientDiffeomorph`: the diffeomorphism `W_O ⧸ G ≃ μ⁻¹(c) ⧸ G_c`.

## Main results

* `contMDiffSMul_orbitFiberProduct`, `properSMul_orbitFiberProduct`,
  `isCancelSMul_orbitFiberProduct`: the action of `G` on `W_O` is smooth, proper and free.
* `orbitFiberProductQuotientDiffeomorph_mk`, `orbitFiberProductQuotientDiffeomorph_symm_mk`: the
  formulas `e [(x, g G_c)] = [g⁻¹ • x]` and `e⁻¹ [z] = [(z, G_c)]`.
* `orbitFiberProductQuotientDiffeomorph_mk_orbitFiberProductDiffeomorph`: `e ∘ π_W ∘ Φ = q_Y`.
* `existsUnique_isSymplectic_mpullback_quotientMk_orbitFiberProduct_eq_sub`: the reduced form on
  `W_O ⧸ G`.

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
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [FiniteDimensional ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {c : Module.Dual ℝ (GroupLieAlgebra I G)} {κ : Type*}

namespace SmoothTwoForm

namespace IsEquivariantMomentMap

/-! ### The action of `G` on the orbit fibre product -/

section Action

variable (h : σ.IsEquivariantMomentMap μ) (b : Basis κ ℝ (GroupLieAlgebra I G))

omit [FiniteDimensional ℝ E'] in
include h in
/-- **The diagonal action preserves the orbit fibre product**: if `μ(x) = ι_O(o)`, then
`μ(k • x) = Ad*_k μ(x) = Ad*_k ι_O(o) = ι_O(k • o)`. -/
theorem smul_mem_orbitFiberProduct (k : G) (p : OrbitFiberProduct μ c b) :
    (fun i ↦ μ (k • p.val).1 (b i)) =
      fun i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c (k • p.val).2 (b i) := by
  refine (components_eq_orbitMap_iff_apply_eq b).2 ?_
  rw [Prod.smul_fst, Prod.smul_snd, h.apply_smul, Representation.orbitMap_smul,
    (components_eq_orbitMap_iff_apply_eq b).1 p.property]

variable (c) in
/-- **The diagonal action of `G` on the orbit fibre product** `W_O`,
`k • (x, o) = (k • x, k • o)`, the restriction of the diagonal action on `M × G ⧸ G_c`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.smul_mem_orbitFiberProduct`). -/
@[instance_reducible]
def orbitFiberProductMulAction : MulAction G (OrbitFiberProduct μ c b) where
  smul k p := ⟨k • p.val, h.smul_mem_orbitFiberProduct b k p⟩
  one_smul p := Subtype.ext (one_smul G p.val)
  mul_smul k k' p := Subtype.ext (mul_smul k k' p.val)

omit [FiniteDimensional ℝ E'] in
/-- The action of `G` on the orbit fibre product is the restriction of the diagonal action on
`M × G ⧸ G_c`. -/
@[simp]
theorem coe_smul_orbitFiberProduct (k : G) (p : OrbitFiberProduct μ c b) :
    letI := h.orbitFiberProductMulAction c b
    ((k • p : OrbitFiberProduct μ c b) : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) =
      k • p.val :=
  (rfl)

/-- **`G` acts freely on the orbit fibre product** when `G_c` acts freely on the level `μ⁻¹(c)`.
If `k • (x, g G_c) = (x, g G_c)`, then `g⁻¹ k g` lies in `G_c` and fixes `g⁻¹ • x`, which lies in
the level, so `g⁻¹ k g = 1`. -/
theorem isCancelSMul_orbitFiberProduct
    [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] :
    letI := h.orbitFiberProductMulAction c b
    IsCancelSMul G (OrbitFiberProduct μ c b) := by
  let _ := h.orbitFiberProductMulAction c b
  refine isCancelSMul_iff_eq_one_of_smul_eq.2 fun k p hk ↦ ?_
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective p.val.2
  have hk' : k • p.val = p.val := congrArg Subtype.val hk
  have hx : k • p.val.1 = p.val.1 := (Prod.smul_fst k p.val).symm.trans (congrArg Prod.fst hk')
  have ho : k • p.val.2 = p.val.2 := (Prod.smul_snd k p.val).symm.trans (congrArg Prod.snd hk')
  -- `k` fixes the coset `g G_c`, so `g⁻¹ k g` lies in `G_c`.
  have hmem : g⁻¹ * (k * g) ∈ (Lie.coadjointRepresentation ℝ I G).stabilizer c := by
    rw [← QuotientGroup.eq, ← smul_eq_mul, ← MulAction.Quotient.smul_mk, hg]
    exact ho.symm
  -- It fixes the point `g⁻¹ • x` of the level, so it is trivial.
  have hfix : (⟨_, hmem⟩ : (Lie.coadjointRepresentation ℝ I G).stabilizer c) •
      (⟨g⁻¹ • p.val.1, h.inv_smul_mem_levelSubMulAction b p hg⟩ : h.levelSubMulAction c) =
        ⟨g⁻¹ • p.val.1, h.inv_smul_mem_levelSubMulAction b p hg⟩ :=
    Subtype.ext (by simp [Subgroup.smul_def, mul_smul, hx])
  have h1 : g⁻¹ * (k * g) = 1 :=
    congrArg Subtype.val (isCancelSMul_iff_eq_one_of_smul_eq.1 ‹_› _ _ hfix)
  simpa [mul_assoc] using congrArg (fun x ↦ g * x * g⁻¹) h1

omit [FiniteDimensional ℝ E'] in
/-- **`G` acts properly on the orbit fibre product** when it acts properly on `M`: the diagonal
action on `M × G ⧸ G_c` is proper, and `W_O` is an invariant subspace. -/
theorem properSMul_orbitFiberProduct [ProperSMul G M] :
    letI := h.orbitFiberProductMulAction c b
    ProperSMul G (OrbitFiberProduct μ c b) :=
  letI := h.orbitFiberProductMulAction c b
  haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  Topology.IsEmbedding.subtypeVal.properSMul fun k p ↦ h.coe_smul_orbitFiberProduct b k p

/-- The fibres of the orbit projection `q_W` are the orbits of the action of `G` on `W_O`, in the
form required by `ProperSMul.diffeomorphOfOrbitSubmersion`. -/
private theorem orbitFiberProductProj_eq_iff_exists_smul_eq (p p' : OrbitFiberProduct μ c b) :
    letI := h.orbitFiberProductMulAction c b
    h.orbitFiberProductProj c b p = h.orbitFiberProductProj c b p' ↔ ∃ k : G, k • p' = p := by
  let _ := h.orbitFiberProductMulAction c b
  rw [eq_comm, h.orbitFiberProductProj_eq_orbitFiberProductProj_iff]
  exact exists_congr fun k ↦ (Subtype.ext_iff (a1 := k • p') (a2 := p)).symm

end Action

section Smooth

variable [Fintype κ] [I.Boundaryless] [I'.Boundaryless] (h : σ.IsEquivariantMomentMap μ)
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  (b : Basis κ ℝ (GroupLieAlgebra I G))

/-- **`G` acts smoothly on the orbit fibre product**, for its transverse fibre-product atlas: the
diagonal action on `M × G ⧸ G_c` is smooth and `W_O` is an embedded submanifold. -/
theorem contMDiffSMul_orbitFiberProduct :
    letI := h.orbitFiberProductMulAction c b
    letI := h.orbitFiberProductChartedSpace c hreg b
    ContMDiffSMul I 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ) ∞ G (OrbitFiberProduct μ c b) :=
  letI := h.orbitFiberProductMulAction c b
  letI := h.orbitFiberProductChartedSpace c hreg b
  (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiffSMul contMDiff_id
    fun k p ↦ h.coe_smul_orbitFiberProduct b k p

end Smooth

/-! ### The quotient manifold `W_O ⧸ G` -/

section Quotient

variable [Fintype κ] [I.Boundaryless] [I'.Boundaryless] [ProperSMul G M]
  (h : σ.IsEquivariantMomentMap μ)
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
  {n : ℕ} (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)
  (b : Basis κ ℝ (GroupLieAlgebra I G))

omit [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] in
/-- The hypotheses of the quotient manifold theorem for the action of `G` on the orbit fibre
product, other than freeness. -/
private theorem quotient_hypotheses :
    letI := h.orbitFiberProductMulAction c b
    letI := h.orbitFiberProductChartedSpace c hreg b
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ) ∞ (OrbitFiberProduct μ c b) ∧
      ContMDiffSMul I 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ) ∞ G (OrbitFiberProduct μ c b) ∧
      ProperSMul G (OrbitFiberProduct μ c b) :=
  ⟨h.isManifold_orbitFiberProduct hreg b, h.contMDiffSMul_orbitFiberProduct hreg b,
    h.properSMul_orbitFiberProduct b⟩

variable (c) in
/-- **The atlas of the quotient `W_O ⧸ G`** of the orbit fibre product by the diagonal action of
`G`: the slice charts of the quotient manifold theorem `ProperSMul.orbitRelQuotientChartedSpace`,
for the free and proper smooth action of `G` on `W_O` with its transverse fibre-product atlas. -/
@[instance_reducible]
def orbitFiberProductQuotientChartedSpace :
    letI := h.orbitFiberProductMulAction c b
    ChartedSpace (ProperSMul.QuotientModelSpace E (Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ))
      (MulAction.orbitRel.Quotient G (OrbitFiberProduct μ c b)) :=
  letI := h.orbitFiberProductMulAction c b
  letI := h.orbitFiberProductChartedSpace c hreg b
  haveI := (h.quotient_hypotheses hreg b).1
  haveI := (h.quotient_hypotheses hreg b).2.1
  haveI := (h.quotient_hypotheses hreg b).2.2
  haveI := h.isCancelSMul_orbitFiberProduct (c := c) b
  ProperSMul.orbitRelQuotientChartedSpace I G 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
      (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
        finrank ℝ (κ → ℝ)) → ℝ) (OrbitFiberProduct μ c b)

/-- **The quotient `W_O ⧸ G` is a smooth manifold**, for the atlas
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductQuotientChartedSpace`. -/
theorem isManifold_orbitFiberProductQuotient :
    letI := h.orbitFiberProductMulAction c b
    letI := h.orbitFiberProductQuotientChartedSpace c hreg b
    IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ)) ∞
      (MulAction.orbitRel.Quotient G (OrbitFiberProduct μ c b)) := by
  let _ := h.orbitFiberProductMulAction c b
  let _ := h.orbitFiberProductChartedSpace c hreg b
  obtain ⟨_, _, _⟩ := h.quotient_hypotheses hreg b
  have := h.isCancelSMul_orbitFiberProduct (c := c) b
  exact ProperSMul.instIsManifoldOrbitRelQuotient

/-- **The orbit projection `π_W : W_O → W_O ⧸ G` is a smooth submersion**, for the transverse
fibre-product atlas of `W_O` and the atlas of the quotient manifold theorem on `W_O ⧸ G`. -/
theorem isSubmersion_quotientMk_orbitFiberProduct :
    letI := h.orbitFiberProductMulAction c b
    letI := h.orbitFiberProductChartedSpace c hreg b
    letI := h.orbitFiberProductQuotientChartedSpace c hreg b
    IsSubmersion 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ)
      𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ)) ∞
      (Quotient.mk (MulAction.orbitRel G (OrbitFiberProduct μ c b))) := by
  let _ := h.orbitFiberProductMulAction c b
  let _ := h.orbitFiberProductChartedSpace c hreg b
  obtain ⟨_, _, _⟩ := h.quotient_hypotheses hreg b
  have := h.isCancelSMul_orbitFiberProduct (c := c) b
  exact ProperSMul.isSubmersion_quotientMk (I := I)

/-- **The quotient of the orbit fibre product by `G` is the reduced space.** With the hypotheses of
the Marsden–Weinstein–Meyer theorem, `G` acts smoothly, freely and properly on
`W_O = {(x, o) ∈ M × O | μ(x) = ι_O(o)}`, so `W_O ⧸ G` is a smooth manifold by the quotient
manifold theorem, and the orbit projection `q_W (x, g G_c) = [g⁻¹ • x]` descends to a
diffeomorphism

`e : W_O ⧸ G ≃ μ⁻¹(c) ⧸ G_c`, `[(x, g G_c)] ↦ [g⁻¹ • x]`

(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductQuotientDiffeomorph_mk`), with
inverse `[z] ↦ [(z, G_c)]`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductQuotientDiffeomorph_symm_mk`). -/
def orbitFiberProductQuotientDiffeomorph :
    letI := h.orbitFiberProductMulAction c b
    letI := h.orbitFiberProductQuotientChartedSpace c hreg b
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    MulAction.orbitRel.Quotient G (OrbitFiberProduct μ c b) ≃ₘ⟮𝓘(ℝ, ProperSMul.QuotientModelSpace E
        (Fin (finrank ℝ E' + finrank ℝ
          (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
            finrank ℝ (κ → ℝ)) → ℝ)),
      𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))⟯
      MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c) :=
  letI := h.orbitFiberProductMulAction c b
  letI := h.orbitFiberProductChartedSpace c hreg b
  haveI := (h.quotient_hypotheses hreg b).1
  haveI := (h.quotient_hypotheses hreg b).2.1
  haveI := (h.quotient_hypotheses hreg b).2.2
  haveI := h.isCancelSMul_orbitFiberProduct (c := c) b
  letI := h.orbitRelQuotientChartedSpace c hreg hn d
  ProperSMul.diffeomorphOfOrbitSubmersion I le_rfl (h.orbitFiberProductProj c b)
    (h.isSubmersion_orbitFiberProductProj hreg hn d b) (h.orbitFiberProductProj_surjective b)
    (h.orbitFiberProductProj_eq_iff_exists_smul_eq b)

/-- **`e ∘ π_W = q_W`**: the diffeomorphism `W_O ⧸ G ≃ μ⁻¹(c) ⧸ G_c` sends the orbit of a point of
the orbit fibre product to its image under the orbit projection `q_W (x, g G_c) = [g⁻¹ • x]`. -/
@[simp]
theorem orbitFiberProductQuotientDiffeomorph_mk (p : OrbitFiberProduct μ c b) :
    letI := h.orbitFiberProductMulAction c b
    letI := h.orbitFiberProductQuotientChartedSpace c hreg b
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    h.orbitFiberProductQuotientDiffeomorph hreg hn d b (Quotient.mk _ p) =
      h.orbitFiberProductProj c b p := by
  let _ := h.orbitFiberProductMulAction c b
  let _ := h.orbitFiberProductChartedSpace c hreg b
  obtain ⟨_, _, _⟩ := h.quotient_hypotheses hreg b
  have := h.isCancelSMul_orbitFiberProduct (c := c) b
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  exact ProperSMul.diffeomorphOfOrbitSubmersion_mk ..

/-- The inverse of the diffeomorphism `W_O ⧸ G ≃ μ⁻¹(c) ⧸ G_c` sends the class of a point `z` of
the level to the orbit of `(z, G_c)`. -/
@[simp]
theorem orbitFiberProductQuotientDiffeomorph_symm_mk (z : h.levelSubMulAction c) :
    letI := h.orbitFiberProductMulAction c b
    letI := h.orbitFiberProductQuotientChartedSpace c hreg b
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    (h.orbitFiberProductQuotientDiffeomorph hreg hn d b).symm (Quotient.mk _ z) =
      Quotient.mk _ (⟨((z : M),
        ((1 : G) : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)),
          (h.components_eq_orbitMap_iff b).2 (by
            simpa using h.mem_levelSubMulAction.1 z.property)⟩ : OrbitFiberProduct μ c b) := by
  let _ := h.orbitFiberProductMulAction c b
  let _ := h.orbitFiberProductQuotientChartedSpace c hreg b
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  rw [← Diffeomorph.symm_apply_apply (h.orbitFiberProductQuotientDiffeomorph hreg hn d b)
    (Quotient.mk _ _), orbitFiberProductQuotientDiffeomorph_mk, h.orbitFiberProductProj_eq b _ rfl]
  exact congrArg _ (congrArg _ (Subtype.ext (by simp)))

/-- **`e ∘ π_W ∘ Φ = q_Y`.** Composed with the orbit projection of `W_O` and the diffeomorphism
`Φ : G ×_{G_c} μ⁻¹(c) ≃ W_O`, `[g, z] ↦ (g • z, g G_c)`, the diffeomorphism
`W_O ⧸ G ≃ μ⁻¹(c) ⧸ G_c` is the projection `[g, z] ↦ [z]` of the balanced product. -/
theorem orbitFiberProductQuotientDiffeomorph_mk_orbitFiberProductDiffeomorph
    (y : BalancedProduct ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
      ((Lie.coadjointRepresentation ℝ I G).stabilizer c).RightTranslation
      (h.levelSubMulAction c)) :
    haveI : T2Space G := I.t2Space_of_lieGroup ∞
    haveI : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
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
    letI := h.orbitFiberProductMulAction c b
    letI := h.orbitFiberProductQuotientChartedSpace c hreg b
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    h.orbitFiberProductQuotientDiffeomorph hreg hn d b
        (Quotient.mk _ (h.orbitFiberProductDiffeomorph hreg hn d b y)) =
      BalancedProduct.orbitProj y := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  exact (h.orbitFiberProductQuotientDiffeomorph_mk hreg hn d b _).trans
    (h.orbitFiberProductProj_orbitFiberProductDiffeomorph hreg hn d b y)

/-- **The reduced form on the quotient of the orbit fibre product.** With the hypotheses of the
Marsden–Weinstein–Meyer theorem, the quotient `W_O ⧸ G` of the orbit fibre product
`W_O = {(x, o) ∈ M × O | μ(x) = ι_O(o)}` by the diagonal action of `G` carries a unique symplectic
form `η` with

`π_W^* η = pr_M^* σ - pr_O^* ω_KKS`

on `W_O`, for the orbit projection `π_W : W_O → W_O ⧸ G` and the two projections
`pr_M (x, o) = x` and `pr_O (x, o) = o`. It is the pullback along the diffeomorphism
`W_O ⧸ G ≃ μ⁻¹(c) ⧸ G_c`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductQuotientDiffeomorph`) of the
reduced form of `existsUnique_isSymplectic_mpullback_orbitFiberProductProj_eq_sub`. -/
theorem existsUnique_isSymplectic_mpullback_quotientMk_orbitFiberProduct_eq_sub
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    letI := h.orbitFiberProductMulAction c b
    letI := h.orbitFiberProductChartedSpace c hreg b
    haveI := h.isManifold_orbitFiberProduct hreg b
    letI := h.orbitFiberProductQuotientChartedSpace c hreg b
    haveI := h.isManifold_orbitFiberProductQuotient hreg b
    ∃! η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E
        (Fin (finrank ℝ E' + finrank ℝ
          (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
            finrank ℝ (κ → ℝ)) → ℝ))
        (MulAction.orbitRel.Quotient G (OrbitFiberProduct μ c b)),
      η.IsSymplectic ∧
        SmoothForm.mpullback _ (h.isSubmersion_quotientMk_orbitFiberProduct hreg b).contMDiff η =
          SmoothForm.mpullback (fun p : OrbitFiberProduct μ c b ↦ p.val.1)
              (contMDiff_fst.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff) σ -
            SmoothForm.mpullback (fun p : OrbitFiberProduct μ c b ↦ p.val.2)
              (contMDiff_snd.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff)
              c.coadjointOrbitForm := by
  let _ := h.orbitFiberProductMulAction c b
  let _ := h.orbitFiberProductChartedSpace c hreg b
  have := h.isManifold_orbitFiberProduct hreg b
  let _ := h.orbitFiberProductQuotientChartedSpace c hreg b
  have := h.isManifold_orbitFiberProductQuotient hreg b
  -- Auxiliary data for the reduced space `μ⁻¹(c) ⧸ G_c`: the closed-subgroup structure of `G_c`.
  have : T2Space G := I.t2Space_of_lieGroup ∞
  let d := Lie.EmbeddedLieSubgroupData.ofIsClosed (I := I)
    (Lie.isClosed_stabilizer_coadjointRepresentation I c)
  have hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) =
      finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) := rfl
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_orbitRelQuotient hreg hn d
  set e := h.orbitFiberProductQuotientDiffeomorph hreg hn d b
  have he : (e ∘ Quotient.mk _ : OrbitFiberProduct μ c b → _) = h.orbitFiberProductProj c b :=
    funext fun p ↦ h.orbitFiberProductQuotientDiffeomorph_mk hreg hn d b p
  -- Pullback along `e` carries the defining identity of the reduced form on `μ⁻¹(c) ⧸ G_c` to that
  -- on `W_O ⧸ G`, since `e ∘ π_W = q_W`.
  have hrw (η : SmoothTwoForm _
      (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c))) :
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_orbitFiberProduct hreg b).contMDiff
          (SmoothForm.mpullback e e.contMDiff η) =
        SmoothForm.mpullback (h.orbitFiberProductProj c b)
          (h.isSubmersion_orbitFiberProductProj hreg hn d b).contMDiff η := by
    rw [SmoothForm.mpullback_mpullback]
    simp only [he]
  obtain ⟨η₀, ⟨hη₀, hη₀q⟩, -⟩ :=
    h.existsUnique_isSymplectic_mpullback_orbitFiberProductProj_eq_sub hreg hn d b hσ hG
  have hsymp : SmoothTwoForm.IsSymplectic (SmoothForm.mpullback e e.contMDiff η₀) :=
    (e.isLocalDiffeomorph.isSymplectic_mpullback_iff e.surjective).2 hη₀
  refine ⟨SmoothForm.mpullback e e.contMDiff η₀, ⟨hsymp, (hrw η₀).trans hη₀q⟩, ?_⟩
  -- Pullback along the surjective submersion `π_W` is injective.
  have hπ := h.isSubmersion_quotientMk_orbitFiberProduct hreg b
  have hinj := SmoothForm.mpullback_injective_of_surjective (F := ℝ) (k := 2) hπ.contMDiff
    Quotient.mk_surjective (hπ.surjective_mfderiv (by simp))
  intro η hηη
  exact hinj (hηη.2.trans ((hrw η₀).trans hη₀q).symm)

end Quotient

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
