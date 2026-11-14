/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.Geometry.Lie.Adjoint.Splitting
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic

import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer

/-!
# The invariant splitting of the Lie algebra at a point with compact stabilizer

Let a Lie group `G` act on `(M, σ)` with a coadjoint-equivariant moment map `μ : M → 𝔤*`, and fix
`p ∈ M` with moment value `ν = μ(p)`. Write `H = G_p` for the stabilizer of `p`, `K = G_ν` for the
coadjoint stabilizer of `ν`, `𝔥 = 𝔤_p` for the isotropy algebra and `𝔨 = 𝔤_ν` for the infinitesimal
coadjoint stabilizer. Equivariance gives `H ≤ K`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.stabilizer_le_stabilizer_coadjointRepresentation`)
and `𝔥 ≤ 𝔨`, and both `𝔥` and `𝔨` are invariant under the adjoint action of `H`.

When `H` is compact, as it is for a proper action, averaging an inner product over `H` therefore
splits

`𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮`,  `𝔥 ⊕ 𝔪 = 𝔨`,

with `Ad(H)`-invariant `𝔪` and `𝔮`
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.exists_adjoint_invariant_splitting`). No
`Ad(G)`-invariant inner product is used, and `G` need be neither compact nor connected. This is
the splitting of the Marle–Guillemin–Sternberg local model `G ×_H (𝔪* × V)` of the action near
the orbit of `p`: `𝔪*` is included into `𝔤*` by extending forms by zero on `𝔥 ⊕ 𝔮`
(`TauCeti.Lie.isIntertwiningMap_dualMap_projectionOnto_coadjointRepresentation`), and the
`𝔮`-summand carries the Kirillov–Kostant–Souriau form of the coadjoint orbit of `ν`.

## Main results

* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.stabilizer_le_stabilizer_coadjointRepresentation`:
  `G_p ≤ G_{μ(p)}`.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.exists_adjoint_invariant_splitting`: for a compact
  stabilizer `G_p`, `Ad(G_p)`-invariant complements `𝔤 = 𝔤_p ⊕ 𝔪 ⊕ 𝔮` with
  `𝔤_p ⊕ 𝔪 = 𝔤_{μ(p)}`.

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

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

local instance : LieGroup I 1 G :=
  LieGroup.of_le (I := I) (G := G) (m := 1) (n := minSmoothness ℝ 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)

/-- **The stabilizer of a point fixes its moment value**: for a coadjoint-equivariant moment map,
the stabilizer `G_p` lies in the coadjoint stabilizer `G_{μ(p)}`. -/
theorem stabilizer_le_stabilizer_coadjointRepresentation (h : σ.IsEquivariantMomentMap μ)
    (p : M) :
    MulAction.stabilizer G p ≤ (Lie.coadjointRepresentation ℝ I G).stabilizer (μ p) :=
  fun g hg ↦ by
    rw [Representation.mem_stabilizer, ← h.apply_smul, MulAction.mem_stabilizer_iff.mp hg]

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G]

/-- **The invariant splitting of the Lie algebra at a point with compact stabilizer.** For a
coadjoint-equivariant moment map `μ` and a point `p` whose stabilizer `H = G_p` is compact, there
are subspaces `𝔪` and `𝔮` of `𝔤`, invariant under the adjoint action of `H`, such that `𝔪`
complements the isotropy algebra `𝔤_p` in the coadjoint stabilizer `𝔤_{μ(p)}` and `𝔮` complements
`𝔤_{μ(p)}` in `𝔤`. Thus `𝔤 = 𝔤_p ⊕ 𝔪 ⊕ 𝔮`, with each summand complementary to the sum of the
other two. -/
theorem exists_adjoint_invariant_splitting (h : σ.IsEquivariantMomentMap μ) (p : M)
    (hp : IsCompact (MulAction.stabilizer G p : Set G)) :
    ∃ 𝔪 𝔮 : Subrepresentation
        ((Lie.adjointRepresentation ℝ I G).comp (MulAction.stabilizer G p).subtype),
      ((InfinitesimalAction.fundamental I G I' M).isotropy p).toSubmodule ⊔ 𝔪.toSubmodule =
          (lieAnnihilator ℝ (GroupLieAlgebra I G) (μ p)).toSubmodule ∧
        IsCompl (lieAnnihilator ℝ (GroupLieAlgebra I G) (μ p)).toSubmodule 𝔮.toSubmodule ∧
        IsCompl ((InfinitesimalAction.fundamental I G I' M).isotropy p).toSubmodule
          (𝔪.toSubmodule ⊔ 𝔮.toSubmodule) ∧
        IsCompl 𝔪.toSubmodule
          (((InfinitesimalAction.fundamental I G I' M).isotropy p).toSubmodule ⊔
            𝔮.toSubmodule) := by
  -- The isotropy algebra and the coadjoint stabilizer, as `Ad(G_p)`-invariant subspaces.
  let 𝔥 : Subrepresentation
      ((Lie.adjointRepresentation ℝ I G).comp (MulAction.stabilizer G p).subtype) :=
    ⟨((InfinitesimalAction.fundamental I G I' M).isotropy p).toSubmodule, fun g _ hξ ↦ by
      simpa only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        Lie.adjointRepresentation_apply, LieSubalgebra.mem_toSubmodule] using
        adjointContinuousLinearMap_mem_isotropy_of_mem_stabilizer g.2 hξ⟩
  let 𝔨 : Subrepresentation
      ((Lie.adjointRepresentation ℝ I G).comp (MulAction.stabilizer G p).subtype) :=
    ⟨(lieAnnihilator ℝ (GroupLieAlgebra I G) (μ p)).toSubmodule, fun g _ hξ ↦ by
      simpa only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        Lie.adjointRepresentation_apply, LieSubalgebra.mem_toSubmodule] using
        Lie.adjointContinuousLinearMap_mem_lieAnnihilator_of_mem_stabilizer
          (h.stabilizer_le_stabilizer_coadjointRepresentation p g.2) hξ⟩
  have hle : 𝔥 ≤ 𝔨 := Subrepresentation.toSubmodule_le_toSubmodule.mp fun _ hξ ↦
    h.toIsMomentMap.isotropy_le_lieAnnihilator (h.momentCocycle_eq_zero p) hξ
  obtain ⟨𝔪, 𝔮, hsup, h𝔨, h𝔥, h𝔪⟩ := Lie.exists_adjoint_invariant_splitting hp hle
  exact ⟨𝔪, 𝔮, congrArg Subrepresentation.toSubmodule hsup,
    Subrepresentation.isCompl_toSubmodule.mpr h𝔨, Subrepresentation.isCompl_toSubmodule.mpr h𝔥,
    Subrepresentation.isCompl_toSubmodule.mpr h𝔪⟩

end TauCeti.SmoothTwoForm.IsEquivariantMomentMap
