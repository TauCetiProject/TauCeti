/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.OrbitFiberProduct.ReducedForm

import TauCeti.Geometry.Manifold.GroupAction.Restrict
import TauCeti.Topology.Algebra.ProperAction.Basic

/-!
# The quotient of the orbit fibre product by `G`

Let a Lie group `G` act smoothly and properly on a manifold `M`, with coadjoint-equivariant moment
map `μ : M → 𝔤*`, let `c` be a regular value of `μ`, and let `O = G ⧸ G_c` be the coadjoint orbit
of `c`, with orbit map `ι_O [g] = Ad*_g c`. The orbit fibre product

`W_O = {(x, o) ∈ M × O | μ(x) = ι_O(o)}`

(`TauCeti.OrbitFiberProduct`) is an embedded submanifold of `M × O`. This file constructs its
quotient by `G` as a manifold of its own and identifies it with the reduced space
`Q = μ⁻¹(c) ⧸ G_c`.

The diagonal action `k • (x, o) = (k • x, k • o)` of `G` on `M × O` preserves `W_O`, since
`μ(k • x) = Ad*_k μ(x)` and `ι_O(k • o) = Ad*_k ι_O(o)`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductMulAction`). On `W_O` this action
is

* smooth, because the inclusion `W_O → M × O` is a smooth embedding
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.contMDiffSMul_orbitFiberProduct`);
* proper, because the diagonal action on `M × O` is proper when the action on `M` is, and `W_O`
  carries the subspace topology
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.properSMul_orbitFiberProduct`);
* free when `G_c` acts freely on the level `μ⁻¹(c)`: if `k` fixes `(x, g G_c)`, then
  `g⁻¹ k g ∈ G_c` fixes the point `g⁻¹ • x` of the level, so `k = 1`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isCancelSMul_orbitFiberProduct`).

The quotient manifold theorem then makes `W_O ⧸ G` a smooth manifold
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductQuotientChartedSpace`) and the
quotient map `π_W : W_O → W_O ⧸ G` a smooth submersion. The orbit projection
`q_W (x, g G_c) = [g⁻¹ • x]` is a surjective smooth submersion `W_O → Q` whose fibres are the
`G`-orbits
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductProj_eq_orbitFiberProductProj_iff`),
so it descends to a diffeomorphism

`e : W_O ⧸ G ≃ Q`, `e [(x, g G_c)] = [g⁻¹ • x]`, with inverse `[z] ↦ [(z, G_c)]`

(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductQuotientDiffeomorph`). Composed
with the diffeomorphism `Φ : G ×_{G_c} μ⁻¹(c) ≃ W_O`, `[g, z] ↦ (g • z, g G_c)`, it gives
`e ∘ π_W ∘ Φ = q_Y`, the projection `[g, z] ↦ [z]` of the balanced product. Finally, for a
symplectic `σ` preserved by `G`, there is a unique symplectic form `η` on `W_O ⧸ G` with

`π_W^* η = pr_M^* σ - pr_O^* ω_KKS`,

for the two projections `pr_M` and `pr_O` of `W_O ⊆ M × O` and the Kirillov–Kostant–Souriau form
`ω_KKS` on `O`. So `W_O ⧸ G` with this form is the orbit-reduced space of `μ⁻¹(O)`. The proof
obtains `η` by pulling back along `e` the form on `μ⁻¹(c) ⧸ G_c` characterized in
`ReducedForm.lean`; this file does not state that `e` is a symplectomorphism.

## Main definitions

All declarations are in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`.

* `orbitFiberProductMulAction`: the diagonal action of `G` on `W_O`.
* `orbitFiberProductQuotientChartedSpace`: the atlas of the quotient manifold `W_O ⧸ G`.
* `orbitFiberProductQuotientDiffeomorph`: the diffeomorphism `e : W_O ⧸ G ≃ μ⁻¹(c) ⧸ G_c`.

## Main results

* `contMDiffSMul_orbitFiberProduct`, `properSMul_orbitFiberProduct`,
  `isCancelSMul_orbitFiberProduct`: the action of `G` on `W_O` is smooth, proper and free.
* `isManifold_orbitFiberProductQuotient`, `isSubmersion_quotientMk_orbitFiberProduct`: `W_O ⧸ G`
  is a smooth manifold and `π_W` is a smooth submersion.
* `orbitFiberProductQuotientDiffeomorph_mk`, `orbitFiberProductQuotientDiffeomorph_symm_mk`: the
  formulas `e [(x, g G_c)] = [g⁻¹ • x]` and `e⁻¹ [z] = [(z, G_c)]`.
* `orbitFiberProductQuotientDiffeomorph_mk_orbitFiberProductDiffeomorph`: `e ∘ π_W ∘ Φ = q_Y`.
* `existsUnique_isSymplectic_mpullback_quotientMk_orbitFiberProduct_eq_sub`: existence and
  uniqueness of the reduced form on `W_O ⧸ G`.

## References

* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 6.1 (orbit reduction and its equivalence with point reduction).
* E. Meinrenken, *Symplectic geometry*, lecture notes, University of Toronto, 2000,
  Proposition 8.6 (the shifting trick).
-/

public section

noncomputable section

open Function Module Manifold Topology
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

/-! ### The diagonal action on the orbit fibre product -/

section Action

variable (h : σ.IsEquivariantMomentMap μ) (b : Basis κ ℝ (GroupLieAlgebra I G))

include h in
omit [FiniteDimensional ℝ E'] in
/-- The diagonal action preserves the orbit fibre product:
`μ(k • x) = Ad*_k μ(x) = Ad*_k ι_O(o) = ι_O(k • o)`. -/
private theorem smul_mem_orbitFiberProduct (k : G) (p : OrbitFiberProduct μ c b) :
    (fun i ↦ μ (k • p.val).1 (b i)) =
      fun i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c (k • p.val).2 (b i) := by
  refine (components_eq_orbitMap_iff_apply_eq b).2 ?_
  rw [Prod.smul_fst, Prod.smul_snd, h.apply_smul, Representation.orbitMap_smul,
    (components_eq_orbitMap_iff_apply_eq b).1 p.property]

variable (c) in
/-- **The diagonal action of `G` on the orbit fibre product**
`k • (x, o) = (k • x, k • o)`, the restriction of the diagonal action of `G` on `M × G ⧸ G_c`
to `W_O = {(x, o) | μ(x) = ι_O(o)}`, which it preserves by equivariance of `μ` and of the orbit
map `ι_O`. -/
@[instance_reducible]
def orbitFiberProductMulAction : MulAction G (OrbitFiberProduct μ c b) where
  smul k p := ⟨k • p.val, h.smul_mem_orbitFiberProduct b k p⟩
  one_smul p := Subtype.ext (one_smul G p.val)
  mul_smul k k' p := Subtype.ext (mul_smul k k' p.val)

omit [FiniteDimensional ℝ E'] in
/-- The diagonal action on the orbit fibre product is the diagonal action on `M × G ⧸ G_c`. -/
@[simp]
theorem coe_smul_orbitFiberProduct (k : G) (p : OrbitFiberProduct μ c b) :
    letI := h.orbitFiberProductMulAction c b
    ((k • p : OrbitFiberProduct μ c b) : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) =
      k • (p : M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) :=
  (rfl)

/-- The fibres of the orbit projection `q_W` are the orbits of the diagonal action on `W_O`, in
the form used by the quotient manifold theorem. -/
private theorem orbitFiberProductProj_eq_iff_exists_smul_eq (p p' : OrbitFiberProduct μ c b) :
    letI := h.orbitFiberProductMulAction c b
    h.orbitFiberProductProj c b p = h.orbitFiberProductProj c b p' ↔ ∃ k : G, k • p' = p := by
  let _ := h.orbitFiberProductMulAction c b
  rw [h.orbitFiberProductProj_eq_orbitFiberProductProj_iff b]
  refine ⟨fun ⟨k, hk⟩ ↦ ⟨k⁻¹, Subtype.ext ?_⟩, fun ⟨k, hk⟩ ↦ ⟨k⁻¹, ?_⟩⟩
  · rw [coe_smul_orbitFiberProduct, ← hk, inv_smul_smul]
  · rw [← hk, coe_smul_orbitFiberProduct, inv_smul_smul]

/-- **The action of `G` on the orbit fibre product is free** when the coadjoint stabilizer `G_c`
acts freely on the level `μ⁻¹(c)`. If `k` fixes `(x, g G_c)`, then `g⁻¹ k g` lies in `G_c` and
fixes the point `g⁻¹ • x` of the level, so `k = 1`. -/
theorem isCancelSMul_orbitFiberProduct
    [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)] :
    letI := h.orbitFiberProductMulAction c b
    IsCancelSMul G (OrbitFiberProduct μ c b) := by
  let _ := h.orbitFiberProductMulAction c b
  refine isCancelSMul_iff_eq_one_of_smul_eq.2 fun k p hk ↦ ?_
  have hk' : k • p.val = p.val := congrArg Subtype.val hk
  have hx : k • p.val.1 = p.val.1 := congrArg Prod.fst hk'
  have ho : k • p.val.2 = p.val.2 := congrArg Prod.snd hk'
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective p.val.2
  rw [← hg, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at ho
  -- The element `(k g)⁻¹ g = g⁻¹ k⁻¹ g` of `G_c` fixes the point `g⁻¹ • x` of the level.
  have hfix : (⟨_, ho⟩ : (Lie.coadjointRepresentation ℝ I G).stabilizer c) •
      (⟨g⁻¹ • p.val.1, h.inv_smul_mem_levelSubMulAction b p hg⟩ : h.levelSubMulAction c) =
      ⟨g⁻¹ • p.val.1, h.inv_smul_mem_levelSubMulAction b p hg⟩ := by
    refine Subtype.ext ?_
    simp [mul_smul, inv_smul_eq_iff.2 hx.symm]
  simpa [mul_assoc, inv_mul_eq_one] using congrArg Subtype.val (IsCancelSMul.eq_one_of_smul hfix)

omit [FiniteDimensional ℝ E'] in
/-- **The action of `G` on the orbit fibre product is proper** when the action on `M` is. The
diagonal action on `M × G ⧸ G_c` is proper, and the orbit fibre product carries the subspace
topology. -/
theorem properSMul_orbitFiberProduct [ProperSMul G M] :
    letI := h.orbitFiberProductMulAction c b
    ProperSMul G (OrbitFiberProduct μ c b) := by
  let _ := h.orbitFiberProductMulAction c b
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  exact IsEmbedding.subtypeVal.properSMul fun _ _ ↦ rfl

variable [Fintype κ] [I.Boundaryless] [I'.Boundaryless]
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))

/-- **The action of `G` on the orbit fibre product is smooth**, for the transverse fibre-product
atlas of `W_O`: its composite with the smooth embedding `W_O → M × G ⧸ G_c` is the smooth diagonal
action. -/
theorem contMDiffSMul_orbitFiberProduct :
    letI := h.orbitFiberProductChartedSpace c hreg b
    letI := h.orbitFiberProductMulAction c b
    ContMDiffSMul I 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ) ∞ G (OrbitFiberProduct μ c b) := by
  let _ := h.orbitFiberProductChartedSpace c hreg b
  let _ := h.orbitFiberProductMulAction c b
  have := ContMDiffSMul.prod_of_smul_eq (I := I) (I' := I')
    (IF' := 𝓘(ℝ, Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)))
    (K := G) (M := M) (N := G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) (n := ∞)
    contMDiff_id contMDiff_id fun _ _ ↦ rfl
  exact (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiffSMul contMDiff_id
    fun _ _ ↦ rfl

end Action

/-! ### The quotient manifold `W_O ⧸ G` -/

section Quotient

variable [Fintype κ] [I.Boundaryless] [I'.Boundaryless] [ProperSMul G M]
  (h : σ.IsEquivariantMomentMap μ)
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
  (b : Basis κ ℝ (GroupLieAlgebra I G))

/-- The hypotheses of the quotient manifold theorem for the diagonal action of `G` on the orbit
fibre product. -/
private theorem quotient_hypotheses :
    letI := h.orbitFiberProductChartedSpace c hreg b
    letI := h.orbitFiberProductMulAction c b
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ) ∞ (OrbitFiberProduct μ c b) ∧
      ContMDiffSMul I 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ) ∞ G (OrbitFiberProduct μ c b) ∧
      ProperSMul G (OrbitFiberProduct μ c b) ∧ IsCancelSMul G (OrbitFiberProduct μ c b) :=
  ⟨h.isManifold_orbitFiberProduct hreg b, h.contMDiffSMul_orbitFiberProduct b hreg,
    h.properSMul_orbitFiberProduct b, h.isCancelSMul_orbitFiberProduct b⟩

variable (c) in
/-- **The atlas of the quotient `W_O ⧸ G`** of the orbit fibre product by the diagonal action of
`G`: the slice charts of the quotient manifold theorem `ProperSMul.orbitRelQuotientChartedSpace`,
for this free and proper smooth action. -/
@[instance_reducible]
def orbitFiberProductQuotientChartedSpace :
    letI := h.orbitFiberProductMulAction c b
    ChartedSpace (ProperSMul.QuotientModelSpace E (Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ))
      (MulAction.orbitRel.Quotient G (OrbitFiberProduct μ c b)) :=
  letI := h.orbitFiberProductChartedSpace c hreg b
  letI := h.orbitFiberProductMulAction c b
  haveI := (h.quotient_hypotheses hreg b).1
  haveI := (h.quotient_hypotheses hreg b).2.1
  haveI := (h.quotient_hypotheses hreg b).2.2.1
  haveI := (h.quotient_hypotheses hreg b).2.2.2
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
  let _ := h.orbitFiberProductChartedSpace c hreg b
  let _ := h.orbitFiberProductMulAction c b
  obtain ⟨_, _, _, _⟩ := h.quotient_hypotheses hreg b
  exact ProperSMul.instIsManifoldOrbitRelQuotient

/-- **The quotient map `π_W : W_O → W_O ⧸ G` is a smooth submersion.** -/
theorem isSubmersion_quotientMk_orbitFiberProduct :
    letI := h.orbitFiberProductChartedSpace c hreg b
    letI := h.orbitFiberProductMulAction c b
    letI := h.orbitFiberProductQuotientChartedSpace c hreg b
    IsSubmersion 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ)
      𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ)) ∞
      (Quotient.mk (MulAction.orbitRel G (OrbitFiberProduct μ c b))) := by
  let _ := h.orbitFiberProductChartedSpace c hreg b
  let _ := h.orbitFiberProductMulAction c b
  obtain ⟨_, _, _, _⟩ := h.quotient_hypotheses hreg b
  exact ProperSMul.isSubmersion_quotientMk

/-! ### The diffeomorphism with the reduced space -/

variable {n : ℕ} (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)

/-- **The quotient of the orbit fibre product by `G` is the reduced space.** With the hypotheses of
the Marsden–Weinstein–Meyer theorem (`G` acts properly on `M`, `c` is a regular value of the
coadjoint-equivariant moment map `μ`, and the coadjoint stabilizer `G_c`, with the Lie group
structure `d`, acts freely on the level `μ⁻¹(c)`), the orbit projection
`q_W (x, g G_c) = [g⁻¹ • x]` descends to a diffeomorphism

`e : W_O ⧸ G ≃ μ⁻¹(c) ⧸ G_c`, `e [(x, g G_c)] = [g⁻¹ • x]`

(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductQuotientDiffeomorph_mk`), with
inverse `[z] ↦ [(z, G_c)]`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductQuotientDiffeomorph_symm_mk`),
for the atlases of the quotient manifold theorem on both sides. Indeed `q_W` is a surjective
smooth submersion whose fibres are the `G`-orbits of `W_O`. -/
def orbitFiberProductQuotientDiffeomorph :
    letI := h.orbitFiberProductMulAction c b
    letI := h.orbitFiberProductQuotientChartedSpace c hreg b
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    MulAction.orbitRel.Quotient G (OrbitFiberProduct μ c b) ≃ₘ⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ)),
      𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))⟯
      MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c) :=
  letI := h.orbitFiberProductChartedSpace c hreg b
  letI := h.orbitFiberProductMulAction c b
  haveI := (h.quotient_hypotheses hreg b).1
  haveI := (h.quotient_hypotheses hreg b).2.1
  haveI := (h.quotient_hypotheses hreg b).2.2.1
  haveI := (h.quotient_hypotheses hreg b).2.2.2
  letI := h.orbitRelQuotientChartedSpace c hreg hn d
  ProperSMul.diffeomorphOfOrbitSubmersion I le_rfl (h.orbitFiberProductProj c b)
    (h.isSubmersion_orbitFiberProductProj hreg hn d b) (h.orbitFiberProductProj_surjective b)
    (h.orbitFiberProductProj_eq_iff_exists_smul_eq b)

/-- `e ∘ π_W = q_W`: the diffeomorphism `e` sends the orbit of `p` to `q_W p`. -/
@[simp]
theorem orbitFiberProductQuotientDiffeomorph_quotientMk (p : OrbitFiberProduct μ c b) :
    letI := h.orbitFiberProductMulAction c b
    letI := h.orbitFiberProductQuotientChartedSpace c hreg b
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    h.orbitFiberProductQuotientDiffeomorph hreg b hn d
        (Quotient.mk (MulAction.orbitRel G (OrbitFiberProduct μ c b)) p) =
      h.orbitFiberProductProj c b p := by
  let _ := h.orbitFiberProductChartedSpace c hreg b
  let _ := h.orbitFiberProductMulAction c b
  obtain ⟨_, _, _, _⟩ := h.quotient_hypotheses hreg b
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  exact ProperSMul.diffeomorphOfOrbitSubmersion_mk I le_rfl _ _ _ _ p

/-- **The formula for `e`**: `e [(x, g G_c)] = [g⁻¹ • x]`. -/
theorem orbitFiberProductQuotientDiffeomorph_mk (x : M) (g : G)
    (hp : ((x, (g : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)) :
      M × G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c) ∈
        {p | (fun i ↦ μ p.1 (b i)) =
          fun i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c p.2 (b i)}) :
    letI := h.orbitFiberProductMulAction c b
    letI := h.orbitFiberProductQuotientChartedSpace c hreg b
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    h.orbitFiberProductQuotientDiffeomorph hreg b hn d
        (Quotient.mk (MulAction.orbitRel G (OrbitFiberProduct μ c b)) ⟨(x, g), hp⟩) =
      Quotient.mk _ ⟨g⁻¹ • x, h.inv_smul_mem_levelSubMulAction b ⟨(x, g), hp⟩ rfl⟩ := by
  rw [orbitFiberProductQuotientDiffeomorph_quotientMk, orbitFiberProductProj_mk]

/-- **The inverse of `e`** sends the orbit `[z]` of a point `z` of the level to the orbit of
`(z, G_c)`. -/
@[simp]
theorem orbitFiberProductQuotientDiffeomorph_symm_mk (z : h.levelSubMulAction c) :
    letI := h.orbitFiberProductMulAction c b
    letI := h.orbitFiberProductQuotientChartedSpace c hreg b
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    (h.orbitFiberProductQuotientDiffeomorph hreg b hn d).symm (Quotient.mk _ z) =
      Quotient.mk (MulAction.orbitRel G (OrbitFiberProduct μ c b))
        ⟨((z : M), ((1 : G) : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c)),
          (h.components_eq_orbitMap_iff b).2
            (by simpa using h.mem_levelSubMulAction.1 z.property)⟩ := by
  let _ := h.orbitFiberProductMulAction c b
  let _ := h.orbitFiberProductQuotientChartedSpace c hreg b
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  rw [← Diffeomorph.toEquiv_coe_symm, Equiv.symm_apply_eq, Diffeomorph.coe_toEquiv,
    orbitFiberProductQuotientDiffeomorph_mk]
  exact congrArg _ (Subtype.ext (by simp))

/-- **`e ∘ π_W ∘ Φ = q_Y`.** The diffeomorphism `e : W_O ⧸ G ≃ μ⁻¹(c) ⧸ G_c`, composed with the
quotient map `π_W` and the diffeomorphism `Φ : G ×_{G_c} μ⁻¹(c) ≃ W_O`, `[g, z] ↦ (g • z, g G_c)`,
is the projection `q_Y [g, z] = [z]` of the balanced product. -/
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
    h.orbitFiberProductQuotientDiffeomorph hreg b hn d
        (Quotient.mk (MulAction.orbitRel G (OrbitFiberProduct μ c b))
          (h.orbitFiberProductDiffeomorph hreg hn d b y)) =
      BalancedProduct.orbitProj y := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
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
  let _ := h.orbitFiberProductMulAction c b
  let _ := h.orbitFiberProductQuotientChartedSpace c hreg b
  let _ := h.orbitRelQuotientChartedSpace c hreg hn d
  rw [orbitFiberProductQuotientDiffeomorph_quotientMk,
    orbitFiberProductProj_orbitFiberProductDiffeomorph]

/-- **The reduced form on `W_O ⧸ G`.** Let a Lie group `G` act smoothly and properly by
symplectomorphisms on a symplectic manifold `(M, σ)`, with coadjoint-equivariant moment map `μ`,
let `c` be a regular value of `μ`, and let the coadjoint stabilizer `G_c` act freely on the level
`μ⁻¹(c)`. Then the quotient `W_O ⧸ G` of the orbit fibre product carries a unique symplectic
form `η` with

`π_W^* η = pr_M^* σ - pr_O^* ω_KKS`

on `W_O`, for the quotient map `π_W`, the two projections `pr_M (x, o) = x` and `pr_O (x, o) = o`,
and the Kirillov–Kostant–Souriau form `ω_KKS` on `O = G ⧸ G_c`. The proof constructs `η` as the
pullback along the diffeomorphism `e : W_O ⧸ G ≃ μ⁻¹(c) ⧸ G_c`, for some embedded Lie subgroup
structure on the closed subgroup `G_c`, of the form on `μ⁻¹(c) ⧸ G_c` characterized in
`existsUnique_isSymplectic_mpullback_orbitFiberProductProj_eq_sub`. -/
theorem existsUnique_isSymplectic_mpullback_quotientMk_orbitFiberProduct_eq_sub
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    letI := h.orbitFiberProductChartedSpace c hreg b
    haveI := h.isManifold_orbitFiberProduct hreg b
    letI := h.orbitFiberProductMulAction c b
    letI := h.orbitFiberProductQuotientChartedSpace c hreg b
    haveI := h.isManifold_orbitFiberProductQuotient hreg b
    ∃! η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace E (Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ))
        (MulAction.orbitRel.Quotient G (OrbitFiberProduct μ c b)),
      η.IsSymplectic ∧
        SmoothForm.mpullback (Quotient.mk (MulAction.orbitRel G (OrbitFiberProduct μ c b)))
            (h.isSubmersion_quotientMk_orbitFiberProduct hreg b).contMDiff η =
          SmoothForm.mpullback (fun p : OrbitFiberProduct μ c b ↦ p.val.1)
              (contMDiff_fst.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff) σ -
            SmoothForm.mpullback (fun p : OrbitFiberProduct μ c b ↦ p.val.2)
              (contMDiff_snd.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff)
              c.coadjointOrbitForm := by
  let _ := h.orbitFiberProductChartedSpace c hreg b
  have := h.isManifold_orbitFiberProduct hreg b
  let _ := h.orbitFiberProductMulAction c b
  let _ := h.orbitFiberProductQuotientChartedSpace c hreg b
  have := h.isManifold_orbitFiberProductQuotient hreg b
  -- Compare with the reduced space `μ⁻¹(c) ⧸ G_c`, for some embedded Lie subgroup structure on
  -- the closed subgroup `G_c`.
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  obtain ⟨d⟩ := Lie.nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed (I := I)
    (Lie.isClosed_stabilizer_coadjointRepresentation I c)
  let _ := h.orbitRelQuotientChartedSpace c hreg rfl d
  have := h.isManifold_orbitRelQuotient hreg rfl d
  have hπ := h.isSubmersion_quotientMk_orbitFiberProduct hreg b
  set e := h.orbitFiberProductQuotientDiffeomorph hreg b rfl d
  have he : ⇑e ∘ Quotient.mk (MulAction.orbitRel G (OrbitFiberProduct μ c b)) =
      h.orbitFiberProductProj c b :=
    funext (h.orbitFiberProductQuotientDiffeomorph_quotientMk hreg b rfl d)
  obtain ⟨η₀, ⟨hη₀, hη₀q⟩, -⟩ :=
    h.existsUnique_isSymplectic_mpullback_orbitFiberProductProj_eq_sub hreg rfl d b hσ hG
  refine ⟨SmoothForm.mpullback e e.contMDiff η₀,
    ⟨(e.isLocalDiffeomorph.isSymplectic_mpullback_iff e.surjective).2 hη₀, ?_⟩,
    fun η hη ↦ ?_⟩
  · rw [SmoothForm.mpullback_mpullback, ← hη₀q]
    simp only [he]
  · -- Pullback along the surjective submersion `π_W` is injective.
    refine SmoothForm.mpullback_injective_of_surjective hπ.contMDiff Quotient.mk_surjective
      (hπ.surjective_mfderiv (by simp)) ?_
    rw [hη.2, SmoothForm.mpullback_mpullback, ← hη₀q]
    simp only [he]

end Quotient

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
