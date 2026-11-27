/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.OrbitLevel
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.OrbitFiberProduct

import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.RegularLevel
import TauCeti.Topology.Constructions.Basic

/-!
# The orbit fibre product as a coisotropic immersed submanifold of `M`

Let a Lie group `G` act smoothly on a manifold `M` with a coadjoint-equivariant moment map
`μ : M → 𝔤*`, let `c` be a regular value of `μ`, and let `O = G ⧸ G_c` be the coadjoint orbit of
`c` with its homogeneous smooth structure and orbit map `ι_O [g] = Ad*_g c`. The orbit fibre product

`W_O = {(x, o) ∈ M × O | μ(x) = ι_O(o)}`

(`TauCeti.OrbitFiberProduct`, a manifold by
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitFiberProductChartedSpace`) is the orbit-level
manifold of orbit reduction at `c`. This file shows that its projection `pr_M : (x, o) ↦ x` to `M`
realizes it as the preimage `μ⁻¹(O)`, a coisotropic immersed submanifold of `M`, embedded when `O`
is embedded in `𝔤*`.

* **The set map.** Since `ι_O` is injective, `pr_M` is injective
  (`TauCeti.injective_fst_orbitFiberProduct`), and its image is `μ⁻¹(ι_O(O))`
  (`TauCeti.range_fst_orbitFiberProduct`).
* **The immersion and its tangent images.** Since `ι_O` is an immersion, so is `pr_M`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isImmersion_fst_orbitFiberProduct`), and its
  tangent image at `(x, o)` is `dμ_x⁻¹(𝔤 · μ(x)) = ker dμ_x + 𝔤 · x`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.range_mfderiv_fst_orbitFiberProduct`). Both are
  proved next to the atlas of `W_O`, from the corresponding facts about transverse fibre products.
* **Coisotropicness.** For a nondegenerate form these tangent images are coisotropic, whether or
  not `c` is coadjoint-fixed
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isCoisotropicMap_fst_orbitFiberProduct`); their
  null directions are the stabilizer directions `𝔤_{μ(x)} · x`
  (`TauCeti.SmoothTwoForm.IsMomentMap.ker_differential_sup_orbitTangent_inf_orthogonal`).
* **The embedding.** If `ι_O` is a topological embedding, then `pr_M` is a homeomorphism onto its
  image, by `Function.Pullback.isEmbedding_fst`, hence a smooth embedding of `W_O` onto `μ⁻¹(O)`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isSmoothEmbedding_fst_orbitFiberProduct`). This
  holds for every compact group, whose coadjoint orbits are compact
  (`isSmoothEmbedding_fst_orbitFiberProduct_of_compactSpace`, in the namespace
  `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`). For a noncompact group the orbit map need not be
  an embedding: a coadjoint orbit need not even be locally closed in `𝔤*`.

## References

* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 6.1 (orbit reduction and the shifting theorem).
* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26 (the preimage of a coadjoint orbit is coisotropic).
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
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {c : Module.Dual ℝ (GroupLieAlgebra I G)} {κ : Type*}

/-! ### The projection to `M` as a map of sets -/

omit [FiniteDimensional ℝ E] [TopologicalSpace M] in
/-- **The projection of the orbit fibre product to `M` is injective**: the point `o` of the
coadjoint orbit over a point `x` of `μ⁻¹(O)` is determined by `ι_O(o) = μ(x)`, since the orbit map
`ι_O` is injective. -/
theorem injective_fst_orbitFiberProduct (b : Basis κ ℝ (GroupLieAlgebra I G)) :
    Injective fun p : OrbitFiberProduct μ c b ↦ p.val.1 := by
  intro p q hpq
  refine Subtype.ext (Prod.ext hpq ((Lie.coadjointRepresentation ℝ I G).orbitMap_injective c ?_))
  rw [← (components_eq_orbitMap_iff_apply_eq b).1 p.property,
    ← (components_eq_orbitMap_iff_apply_eq b).1 q.property]
  exact congrArg μ hpq

omit [FiniteDimensional ℝ E] [TopologicalSpace M] in
/-- **The image of the projection of the orbit fibre product to `M`** is the preimage `μ⁻¹(O)` of
the coadjoint orbit `O = ι_O(G ⧸ G_c)` of `c`. -/
theorem range_fst_orbitFiberProduct (b : Basis κ ℝ (GroupLieAlgebra I G)) :
    Set.range (fun p : OrbitFiberProduct μ c b ↦ p.val.1) =
      μ ⁻¹' Set.range ((Lie.coadjointRepresentation ℝ I G).orbitMap c) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.val.2, ((components_eq_orbitMap_iff_apply_eq b).1 p.property).symm⟩
  · rintro ⟨o, ho⟩
    exact ⟨⟨(x, o), (components_eq_orbitMap_iff_apply_eq (p := (x, o)) b).2 ho.symm⟩, rfl⟩

namespace SmoothTwoForm

namespace IsEquivariantMomentMap

variable [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  [FiniteDimensional ℝ E'] [Fintype κ] [I.Boundaryless] [I'.Boundaryless]
  (h : σ.IsEquivariantMomentMap μ)
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  (b : Basis κ ℝ (GroupLieAlgebra I G))

/-! ### Coisotropicness -/

/-- **The preimage of a coadjoint orbit is coisotropic.** For a nondegenerate form and a
coadjoint-equivariant moment map with regular value `c`, the projection of the orbit fibre product
`W_O` to `M`, an injective immersion onto `μ⁻¹(O)`, is a coisotropic map, whether or not `c` is
coadjoint-fixed. -/
theorem isCoisotropicMap_fst_orbitFiberProduct (hσ : σ.IsNondegenerate) :
    letI := h.orbitFiberProductChartedSpace c hreg b
    hσ.IsCoisotropicMap 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ)
      (fun p : OrbitFiberProduct μ c b ↦ p.val.1) :=
  letI := h.orbitFiberProductChartedSpace c hreg b
  h.toIsMomentMap.isCoisotropicMap_of_range_mfderiv_eq hσ
    (fun p ↦ h.momentCocycle_eq_zero p.val.1) (h.range_mfderiv_fst_orbitFiberProduct hreg b)

/-! ### The embedding -/

/-- **The orbit fibre product is the embedded submanifold `μ⁻¹(O)` when `O` is embedded.** If the
orbit map `ι_O`, read in the basis `b`, is a topological embedding, then the projection of the
orbit fibre product `W_O` to `M` is a smooth embedding with image `μ⁻¹(O)`
(`TauCeti.range_fst_orbitFiberProduct`). -/
theorem isSmoothEmbedding_fst_orbitFiberProduct
    (hO : IsEmbedding fun o : G ⧸ (Lie.coadjointRepresentation ℝ I G).stabilizer c ↦
      fun i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c o (b i)) :
    letI := h.orbitFiberProductChartedSpace c hreg b
    IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ) I' ∞
      (fun p : OrbitFiberProduct μ c b ↦ p.val.1) :=
  letI := h.orbitFiberProductChartedSpace c hreg b
  ⟨h.isImmersion_fst_orbitFiberProduct hreg b,
    Function.Pullback.isEmbedding_fst (h.toIsMomentMap.contMDiff_components b).continuous hO⟩

/-- **For a compact group, the orbit fibre product is the embedded submanifold `μ⁻¹(O)`.** The
coadjoint orbit of a compact group is compact, so its orbit map, read in the basis `b` as a
continuous injection into the Hausdorff space `ℝ^κ`, is an embedding, and the projection of the
orbit fibre product `W_O` to `M` is a smooth embedding with image `μ⁻¹(O)`. -/
theorem isSmoothEmbedding_fst_orbitFiberProduct_of_compactSpace [CompactSpace G] :
    letI := h.orbitFiberProductChartedSpace c hreg b
    IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ) I' ∞
      (fun p : OrbitFiberProduct μ c b ↦ p.val.1) := by
  refine h.isSmoothEmbedding_fst_orbitFiberProduct hreg b
    ((c.contMDiff_orbitMap_coadjointRepresentation_components b).continuous.isClosedEmbedding
      fun o o' hoo' ↦ ?_).isEmbedding
  exact (Lie.coadjointRepresentation ℝ I G).orbitMap_injective c
    (b.ext fun i ↦ congrFun hoo' i)

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
