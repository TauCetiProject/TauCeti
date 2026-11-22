/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer
public import TauCeti.Geometry.Lie.Adjoint.Splitting
public import TauCeti.Geometry.Lie.FundamentalVectorField.Isotropy
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.LevelAction

/-!
# The invariant splitting of the Lie algebra at a point with compact stabilizer

Let a Lie group `G` act on `(M, σ)` with a coadjoint-equivariant moment map `μ : M → 𝔤*`, and fix
`p ∈ M` with moment value `ν = μ(p)`. Write `H = G_p` for the stabilizer of `p`, `K = G_ν` for the
coadjoint stabilizer of `ν`, `𝔥 = 𝔤_p` for the isotropy algebra and `𝔨 = 𝔤_ν` for the infinitesimal
coadjoint stabilizer. Equivariance gives `H ≤ K`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.stabilizer_le_stabilizer_coadjointRepresentation`)
and `𝔥 ≤ 𝔨` (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.isotropy_le_lieAnnihilator`), and both
`𝔥` and `𝔨` are subrepresentations of the adjoint representation of `H`
(`TauCeti.isotropySubrepresentation`, `TauCeti.Lie.lieAnnihilatorSubrepresentation`), with
`𝔥 ≤ 𝔨` as subrepresentations (`isotropySubrepresentation_le_lieAnnihilatorSubrepresentation` in
the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`).

When `H` is compact, as it is for a proper action, `𝔤` therefore splits as

`𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮`,  `𝔥 ⊕ 𝔪 = 𝔨`,

with `Ad(H)`-invariant `𝔪` and `𝔮`
(`exists_isotropySubrepresentation_sup_eq_lieAnnihilatorSubrepresentation_and_isCompl_of_isCompact`
in the same namespace). No `Ad(G)`-invariant inner product is used, and `G` need be neither
compact nor connected. The point-level splitting
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_subrepresentation_complements` gives such
complements under other hypotheses: a nondegenerate two-form preserved by `H` and a vanishing
moment cocycle at `p`, from which the symplectic linear algebra at `p` gives `𝔤_p ≤ 𝔤_{μ(p)}`. Here coadjoint equivariance of `μ` alone gives that inclusion, and `σ` need not be
nondegenerate. This is the splitting of the Marle–Guillemin–Sternberg local model
`G ×_H (𝔪* × V)` of the action near the orbit of `p`: `𝔪*` is included into `𝔤*` by extending
forms by zero on `𝔥 ⊕ 𝔮`
(`TauCeti.Lie.isIntertwiningMap_dualMap_projectionOnto_coadjointRepresentation`), and the
`𝔮`-summand carries the Kirillov–Kostant–Souriau form of the coadjoint orbit of `ν`.

## Main results

Both in the namespace `TauCeti.SmoothTwoForm.IsEquivariantMomentMap`:

* `isotropySubrepresentation_le_lieAnnihilatorSubrepresentation`: `𝔤_p ≤ 𝔤_{μ(p)}` as
  subrepresentations of the adjoint representation of a subgroup of `G_p`.
* For a compact stabilizer `G_p`, `Ad(G_p)`-invariant complements `𝔤 = 𝔤_p ⊕ 𝔪 ⊕ 𝔮` with
  `𝔤_p ⊕ 𝔪 = 𝔤_{μ(p)}`:
  `exists_isotropySubrepresentation_sup_eq_lieAnnihilatorSubrepresentation_and_isCompl_of_isCompact`

## References

* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
* V. Guillemin and S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics*, Math. Phys. Stud. 6, Reidel (1984), 161–175.
* J.-P. Ortega and T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in
  Mathematics 222, Birkhäuser (2004), Section 7.2.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsEquivariantMomentMap

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

attribute [local instance] lieGroupOne

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G]

/-- **The isotropy algebra lies in the coadjoint stabilizer, as subrepresentations.** For a
coadjoint-equivariant moment map `μ` and a subgroup `K` of the stabilizer `G_p`, the isotropy
algebra `𝔤_p` lies in the infinitesimal coadjoint stabilizer `𝔤_{μ(p)}` as subrepresentations of
the adjoint representation of `K`. -/
theorem isotropySubrepresentation_le_lieAnnihilatorSubrepresentation
    (h : σ.IsEquivariantMomentMap μ) {p : M} {K : Subgroup G} (hK : K ≤ MulAction.stabilizer G p) :
    isotropySubrepresentation I I' p hK ≤
      Lie.lieAnnihilatorSubrepresentation (μ p)
        (hK.trans (h.stabilizer_le_stabilizer_coadjointRepresentation p)) := fun _ hξ ↦
  Lie.mem_lieAnnihilatorSubrepresentation_iff.mpr
    (h.isotropy_le_lieAnnihilator p (mem_isotropySubrepresentation_iff.mp hξ))

/-- **The invariant splitting of the Lie algebra at a point with compact stabilizer.** For a
coadjoint-equivariant moment map `μ` and a point `p` whose stabilizer `H = G_p` is compact, there
are subrepresentations `𝔪` and `𝔮` of the adjoint representation of `H` such that `𝔪`
complements the isotropy algebra `𝔤_p` in the coadjoint stabilizer `𝔤_{μ(p)}` and `𝔮` complements
`𝔤_{μ(p)}` in `𝔤`. Thus `𝔤 = 𝔤_p ⊕ 𝔪 ⊕ 𝔮`, with each summand complementary to the sum of the
other two. -/
theorem
    exists_isotropySubrepresentation_sup_eq_lieAnnihilatorSubrepresentation_and_isCompl_of_isCompact
    (h : σ.IsEquivariantMomentMap μ) (p : M) (hp : IsCompact (MulAction.stabilizer G p : Set G)) :
    ∃ 𝔪 𝔮 : Subrepresentation
        ((Lie.adjointRepresentation ℝ I G).comp (MulAction.stabilizer G p).subtype),
      isotropySubrepresentation I I' p le_rfl ⊔ 𝔪 =
          Lie.lieAnnihilatorSubrepresentation (μ p)
            (h.stabilizer_le_stabilizer_coadjointRepresentation p) ∧
        IsCompl (Lie.lieAnnihilatorSubrepresentation (μ p)
          (h.stabilizer_le_stabilizer_coadjointRepresentation p)) 𝔮 ∧
        IsCompl (isotropySubrepresentation I I' p le_rfl) (𝔪 ⊔ 𝔮) ∧
        IsCompl 𝔪 (isotropySubrepresentation I I' p le_rfl ⊔ 𝔮) :=
  Lie.exists_sup_eq_and_isCompl_of_isCompact hp
    (h.isotropySubrepresentation_le_lieAnnihilatorSubrepresentation le_rfl)

end TauCeti.SmoothTwoForm.IsEquivariantMomentMap
