/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.OrbitLevel
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.OrbitFiberProduct

import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Symplectic.Coadjoint.Orbit
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
* **The immersion.** A tangent vector of `W_O` is a pair `(v, w)` with `dμ(v) = dι_O(w)`. Since
  `dι_O` is injective (`Module.Dual.injective_mfderiv_orbitMap_coadjointRepresentation_components`),
  `v = 0` forces `w = 0`, so `pr_M` is an immersion
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isImmersion_fst_orbitFiberProduct`).
* **The tangent images.** The image of `dι_O` at `o` is the tangent space `𝔤 · ι_O(o)` of the
  coadjoint orbit (`Module.Dual.range_mfderiv_orbitMap_coadjointRepresentation_components`), so the
  tangent image of `pr_M` at `(x, o)` is `dμ_x⁻¹(𝔤 · μ(x)) = ker dμ_x + 𝔤 · x`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.range_mfderiv_fst_orbitFiberProduct`).
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

/-! ### The immersion and its tangent images -/

/-- **The projection of the orbit fibre product to `M` has injective differential.** A tangent
vector `ξ` of `W_O` with projections `v` and `w` satisfies `dμ(v) = dι_O(w)`, and `dι_O` is
injective, so `v = 0` forces `w = 0`, and then `ξ = 0`. -/
theorem injective_mfderiv_fst_orbitFiberProduct (p : OrbitFiberProduct μ c b) :
    letI := h.orbitFiberProductChartedSpace c hreg b
    Injective (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ) I'
      (fun p : OrbitFiberProduct μ c b ↦ p.val.1) p) := by
  let _ := h.orbitFiberProductChartedSpace c hreg b
  have hemb := h.isSmoothEmbedding_coe_orbitFiberProduct hreg b
  have hval := (hemb.contMDiff p).mdifferentiableAt (by simp)
  refine (injective_iff_map_eq_zero _).2 fun ξ hξ ↦ ?_
  have hsnd := h.mfderiv_components_mfderiv_fst_orbitFiberProduct hreg b p ξ
  rw [hξ, map_zero] at hsnd
  have hsnd' := (injective_iff_map_eq_zero _).1
    (c.injective_mfderiv_orbitMap_coadjointRepresentation_components b p.val.2) _ hsnd.symm
  -- The inclusion of `W_O` has injective differential, and both components of `dι ξ` vanish.
  refine (injective_iff_map_eq_zero _).1 ((hemb.isImmersion.isImmersionAt p).mfderiv_injective
    (by simp)) ξ (Prod.ext ?_ ?_)
  · rw [← hval.mfderiv_fst_apply]
    exact hξ
  · rw [← hval.mfderiv_snd_apply]
    exact hsnd'

/-- **The projection of the orbit fibre product to `M` is an immersion.** -/
theorem isImmersion_fst_orbitFiberProduct :
    letI := h.orbitFiberProductChartedSpace c hreg b
    IsImmersion 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ) I' ∞
      (fun p : OrbitFiberProduct μ c b ↦ p.val.1) :=
  letI := h.orbitFiberProductChartedSpace c hreg b
  haveI := h.isManifold_orbitFiberProduct hreg b
  (contMDiff_fst.comp (h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff
    ).isImmersion_of_injective_mfderiv (by simp) (h.injective_mfderiv_fst_orbitFiberProduct hreg b)

/-- **The tangent images of the projection of the orbit fibre product to `M`.** At `(x, o)`, the
differential of `pr_M` has as image the space `dμ_x⁻¹(𝔤 · μ(x)) = ker dμ_x + 𝔤 · x` of vectors that
`dμ_x` sends into the tangent space of the coadjoint orbit `O` at `μ(x)`: the tangent space of the
preimage `μ⁻¹(O)`. -/
theorem range_mfderiv_fst_orbitFiberProduct (p : OrbitFiberProduct μ c b) :
    letI := h.orbitFiberProductChartedSpace c hreg b
    LinearMap.range (mfderiv 𝓘(ℝ, Fin (finrank ℝ E' + finrank ℝ
        (Subgroup.QuotientModelSpace I ((Lie.coadjointRepresentation ℝ I G).stabilizer c)) -
          finrank ℝ (κ → ℝ)) → ℝ) I'
      (fun p : OrbitFiberProduct μ c b ↦ p.val.1) p).toLinearMap =
      (LinearMap.range (μ p.val.1).coadjointTangentMap).comap (h.differential p.val.1) := by
  let _ := h.orbitFiberProductChartedSpace c hreg b
  have hval := ((h.isSmoothEmbedding_coe_orbitFiberProduct hreg b).contMDiff p).mdifferentiableAt
    (by simp)
  have hxo : μ p.val.1 = (Lie.coadjointRepresentation ℝ I G).orbitMap c p.val.2 :=
    (components_eq_orbitMap_iff_apply_eq b).1 p.property
  have hT := c.range_mfderiv_orbitMap_coadjointRepresentation_components b p.val.2
  ext v
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, Submodule.mem_comap]
  constructor
  · rintro ⟨ξ, rfl⟩
    -- The `O`-component of `ξ` is moved by `dι_O` along some `⁅Z, ι_O(o)⁆`.
    obtain ⟨Z, hZ⟩ : _ ∈ Set.range fun Z : GroupLieAlgebra I G ↦
        fun i ↦ (⁅Z, (Lie.coadjointRepresentation ℝ I G).orbitMap c p.val.2⁆ : Dual ℝ _) (b i) :=
      hT ▸ Set.mem_range_self _
    refine ⟨Submodule.Quotient.mk Z, b.ext fun i ↦ ?_⟩
    rw [Module.Dual.coadjointTangentMap_mk, hxo, ← h.toIsMomentMap.mfderiv_components_apply,
      h.mfderiv_components_mfderiv_fst_orbitFiberProduct hreg b p ξ, ← hZ]
  · rintro ⟨u, hu⟩
    obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨w, hw⟩ : (fun i ↦ (⁅Z, (Lie.coadjointRepresentation ℝ I G).orbitMap c p.val.2⁆ :
        Dual ℝ _) (b i)) ∈ Set.range (mfderiv _ 𝓘(ℝ, κ → ℝ)
          (fun o i ↦ (Lie.coadjointRepresentation ℝ I G).orbitMap c o (b i)) p.val.2) :=
      hT ▸ Set.mem_range_self Z
    -- The pair `(v, w)` is tangent to `W_O`, and `v` is the `M`-component of its preimage.
    obtain ⟨ξ, hξ⟩ := (h.mem_range_mfderiv_coe_orbitFiberProduct_iff hreg b p (v, w)).2
      (funext fun i ↦ by
        rw [h.toIsMomentMap.mfderiv_components_apply, ← hu, Module.Dual.coadjointTangentMap_mk,
          hxo]
        exact (congrFun hw i).symm)
    refine ⟨ξ, ?_⟩
    rw [hval.mfderiv_fst_apply]
    exact congrArg Prod.fst hξ

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
