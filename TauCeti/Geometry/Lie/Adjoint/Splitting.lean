/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.RepresentationTheory.InvariantForm.Orthogonal
import TauCeti.Geometry.Lie.Adjoint.InvariantForm
import TauCeti.RepresentationTheory.Dual

/-!
# Invariant splittings of a Lie algebra along a compact subgroup

Let `H` be a compact subgroup of a Lie group `G`, acting on the Lie algebra
`𝔤 = GroupLieAlgebra I G` by the adjoint action, and let `𝔥 ≤ 𝔨` be `Ad(H)`-invariant subspaces of
`𝔤`. Averaging an inner product over `H`
(`TauCeti.Lie.exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant_of_isCompact`) and taking
orthogonal complements gives `Ad(H)`-invariant subspaces `𝔪` and `𝔮` with

`𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮`,  `𝔥 ⊕ 𝔪 = 𝔨`,

so that `𝔪` complements `𝔥` in `𝔨` and `𝔮` complements `𝔨` in `𝔤`
(`TauCeti.Lie.exists_adjoint_invariant_splitting`). Neither `G` nor `H` need be connected, and no
`Ad(G)`-invariant inner product is assumed or produced; for noncompact `G` there need not be one.

A complement determines the inclusion of the dual of each summand into `𝔤*`: a linear form on a
summand is extended by zero on the complementary sum, that is, composed with the projection along
it. For invariant summands this inclusion intertwines the dual of the adjoint action of `H` on the
summand with the coadjoint action of `H` on `𝔤*`
(`TauCeti.Lie.isIntertwiningMap_dualMap_projectionOnto_coadjointRepresentation`). Applied to the
splitting above, it includes `𝔥*` and `𝔪*` equivariantly into `𝔤*`.

This is the linear algebra of the local model of a Hamiltonian action near an orbit with compact
stabilizer `H` (the Marle–Guillemin–Sternberg normal form), where `𝔨` is the Lie algebra of the
coadjoint stabilizer of the moment map value, which contains `𝔥`.

## Main results

* `TauCeti.Lie.exists_adjoint_invariant_splitting`: `Ad(H)`-invariant complements
  `𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮` adapted to a flag `𝔥 ≤ 𝔨` of invariant subspaces.
* `TauCeti.Lie.isIntertwiningMap_dualMap_projectionOnto_coadjointRepresentation`: extension by
  zero along an invariant complement includes the dual of an invariant summand into `𝔤*`
  equivariantly for the coadjoint action.

## References

* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
* V. Guillemin and S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics*, Math. Phys. Stud. 6, Reidel (1984), 161–175.
* J.-P. Ortega and T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in
  Mathematics 222, Birkhäuser (2004), Section 7.2.
-/

public section

namespace TauCeti.Lie

open scoped ContDiff Manifold

section Dual

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners 𝕜 E H'}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H' G] [Group G] [LieGroup I 1 G]

/-- **Equivariant inclusion of the dual of an invariant summand.** Let `𝔰 ⊕ 𝔱 = 𝔤` be
complementary subspaces invariant under the adjoint action of a subgroup `H`. Extending linear
forms on `𝔰` by zero on `𝔱`, that is, composing them with the projection onto `𝔰` along `𝔱`,
intertwines the dual of the adjoint action of `H` on `𝔰` with the coadjoint action of `H` on
`𝔤*`. -/
theorem isIntertwiningMap_dualMap_projectionOnto_coadjointRepresentation {H : Subgroup G}
    {𝔰 𝔱 : Subrepresentation ((adjointRepresentation 𝕜 I G).comp H.subtype)} (h : IsCompl 𝔰 𝔱) :
    Representation.IsIntertwiningMap 𝔰.toRepresentation.dual
      ((coadjointRepresentation 𝕜 I G).comp H.subtype)
      (𝔰.toSubmodule.projectionOnto 𝔱.toSubmodule
        (Subrepresentation.isCompl_toSubmodule.mpr h)).dualMap := by
  refine ⟨fun g η ↦ LinearMap.ext fun X ↦ ?_⟩
  rw [(Subrepresentation.isIntertwiningMap_dualMap_projectionOnto h).isIntertwining g η,
    Representation.dual_comp]
  simp only [MonoidHom.coe_comp, Function.comp_apply, Representation.dual_apply,
    Module.Dual.transpose_apply, LinearMap.comp_apply, coadjointRepresentation_apply,
    adjointRepresentation_apply, Subgroup.coe_subtype, LinearMap.dualMap_apply]

end Dual

section Splitting

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H' G] [Group G] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **Invariant splittings of the Lie algebra along a compact subgroup.** Let `H` be a compact
subgroup of a Lie group `G` and `𝔥 ≤ 𝔨` subspaces of `𝔤` invariant under `Ad(H)`. There are
`Ad(H)`-invariant subspaces `𝔪` and `𝔮` with `𝔥 ⊕ 𝔪 = 𝔨` and `𝔨 ⊕ 𝔮 = 𝔤`, so that
`𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮` and each summand is complementary to the sum of the other two. They are the
orthogonal complements `𝔪 = 𝔨 ⊓ 𝔥ᗮ` and `𝔮 = 𝔨ᗮ` for an inner product averaged over `H`. -/
theorem exists_adjoint_invariant_splitting {H : Subgroup G} (hH : IsCompact (H : Set G))
    {𝔥 𝔨 : Subrepresentation ((adjointRepresentation ℝ I G).comp H.subtype)} (h𝔥𝔨 : 𝔥 ≤ 𝔨) :
    ∃ 𝔪 𝔮 : Subrepresentation ((adjointRepresentation ℝ I G).comp H.subtype),
      𝔥 ⊔ 𝔪 = 𝔨 ∧ IsCompl 𝔨 𝔮 ∧ IsCompl 𝔥 (𝔪 ⊔ 𝔮) ∧ IsCompl 𝔪 (𝔥 ⊔ 𝔮) := by
  obtain ⟨b, hsymm, hpos, hAd⟩ :=
    exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant_of_isCompact (I := I) hH
  have hB : TauCeti.Representation.IsInvariantForm
      ((adjointRepresentation ℝ I G).comp H.subtype) b.toBilinForm :=
    TauCeti.Representation.isInvariantForm_iff.mpr fun g X Y ↦ by
      simpa only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        adjointRepresentation_apply, ContinuousLinearMap.toBilinForm_apply] using hAd g g.2 X Y
  have hrefl : b.toBilinForm.IsRefl := fun X Y hXY ↦ by
    rwa [ContinuousLinearMap.toBilinForm_apply, hsymm] at hXY
  have hani : b.toBilinForm.toQuadraticMap.Anisotropic := fun X hX ↦ by
    by_contra hne
    exact (hpos X hne).ne' hX
  exact ⟨𝔨 ⊓ hB.orthogonalSubrepresentation 𝔥, hB.orthogonalSubrepresentation 𝔨,
    hB.sup_inf_orthogonalSubrepresentation hani h𝔥𝔨,
    hB.isCompl_orthogonalSubrepresentation hani 𝔨,
    hB.isCompl_inf_orthogonalSubrepresentation_sup hani h𝔥𝔨,
    hB.isCompl_sup_inf_orthogonalSubrepresentation hani hrefl h𝔥𝔨⟩

end Splitting

end TauCeti.Lie
