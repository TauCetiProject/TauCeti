/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.MomentMap
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.ReducedSpace

import TauCeti.Geometry.Manifold.GroupAction.Restrict
import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Naturality

/-!
# Commuting symmetries of the Marsden–Weinstein–Meyer reduced space

Let a Lie group `G` act smoothly and properly by symplectomorphisms on a symplectic manifold
`(M, σ)`, with coadjoint-equivariant moment map `μ : M → 𝔤*`, let `c` be a regular value of `μ`
such that the coadjoint stabilizer `G_c` acts freely on the level `Z = μ⁻¹(c)`, and let
`π : Z → Z / G_c` be the projection onto the reduced space, which carries the reduced symplectic
form `ω_red` with `π^* ω_red = i^* σ`
(`IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_quotientMk_eq_mpullback`).

A second group `L` acting on `M` by symplectomorphisms which commute with the action of `G` and
preserve `μ` is a symmetry of the reduction. This file shows that it acts on the reduced space:

* `L` preserves the level `Z`, and its restriction to `Z`
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelMulAction`) commutes with the action of
  `G_c`, so it descends to an action `l • [z] = [l • z]` on `Z / G_c`
  (`MulAction.orbitRel.Quotient.instMulActionOfSMulCommClass`).
* If `L` acts on `M` by smooth maps, so does it on the reduced space
  (`IsEquivariantMomentMap.contMDiffConstSMul_orbitRelQuotient_levelMulAction`), and if `L` is a
  Lie group acting smoothly on `M`, its action on the reduced space is smooth
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.contMDiffSMul_orbitRelQuotient_levelMulAction`),
  being descended along the submersion `(l, z) ↦ (l, [z])`.
* If `L` acts by smooth maps preserving `σ`, it preserves the reduced form
  (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback_smul_orbitRelQuotient_eq_self`): every
  form `η` on `Z / G_c` with `π^* η = i^* σ` is `L`-invariant.
* If the action of `L` on `(M, σ)` is Hamiltonian, with a group-level moment map `ν : M → 𝔩*`
  invariant under `G_c` along the level, then `ν` descends to the unique map `ν'` on `Z / G_c`
  with `ν' ∘ π = ν ∘ i`, and `ν'` is a group-level moment map of the reduced action for `ω_red`
  (`IsEquivariantMomentMap.existsUnique_comp_quotientMk_eq_and_isEquivariantMomentMap`).

Typical instances are the residual symmetries of reduction: for a Hamiltonian action of a product
`G × L`, the factor `L` acts on the reduction by `G`, and for a Hamiltonian torus action, the
torus acts on the reduction by any subtorus. Freeness and properness of the action of `L` are not
needed, and `L` may be any monoid acting by smooth maps, with no topology, until the joint
smoothness of its action or its moment map enters.

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* J.-P. Ortega, T. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics 222,
  Birkhäuser, 2004, Section 6.1 (residual symmetries of reduced spaces).
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsEquivariantMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {c : Module.Dual ℝ (GroupLieAlgebra I G)} {n : ℕ}
  {EL HL L : Type*} [NormedAddCommGroup EL] [NormedSpace ℝ EL] [TopologicalSpace HL]
  {IL : ModelWithCorners ℝ EL HL}

variable (h : σ.IsEquivariantMomentMap μ)

section Monoid

variable [Monoid L] [MulAction L M]

/-! ### The action on the level -/

omit [I'.Boundaryless] in
variable (c) in
/-- **A symmetry preserving `μ` acts on the level.** An action of `L` on `M` with
`μ (l • x) = μ x` preserves the level `μ⁻¹(c)`, and restricts to an action on it. -/
@[instance_reducible]
def levelMulAction (hμL : ∀ (l : L) (x : M), μ (l • x) = μ x) :
    MulAction L (h.levelSubMulAction c) where
  smul l z := ⟨l • (z : M), h.mem_levelSubMulAction.2
    ((hμL l z).trans (h.mem_levelSubMulAction.1 z.property))⟩
  one_smul z := Subtype.ext (one_smul L (z : M))
  mul_smul l l' z := Subtype.ext (mul_smul l l' (z : M))

omit [I'.Boundaryless] in
/-- The action of `L` on the level is the restriction of its action on `M`. -/
@[simp]
theorem coe_smul_levelMulAction (hμL : ∀ (l : L) (x : M), μ (l • x) = μ x) (l : L)
    (z : h.levelSubMulAction c) :
    letI := h.levelMulAction c hμL
    ((l • z : h.levelSubMulAction c) : M) = l • (z : M) :=
  (rfl)

omit [I'.Boundaryless] in
variable (c) in
/-- **The symmetry commutes with the stabilizer on the level.** Since `L` commutes with `G`, its
action on the level `μ⁻¹(c)` commutes with that of the coadjoint stabilizer `G_c`. -/
theorem smulCommClass_levelMulAction [SMulCommClass L G M]
    (hμL : ∀ (l : L) (x : M), μ (l • x) = μ x) :
    letI := h.levelMulAction c hμL
    SMulCommClass L ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c) :=
  letI := h.levelMulAction c hμL
  ⟨fun l k z ↦ Subtype.ext (smul_comm l (k : G) (z : M))⟩

variable (c) in
/-- **The symmetry acts by smooth maps on a regular level.** If `L` acts on `M` by smooth maps, it
acts by smooth maps on the regular level `μ⁻¹(c)`, with the atlas
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelSubMulActionChartedSpace`. -/
theorem contMDiffConstSMul_levelMulAction [ContMDiffConstSMul I' ∞ L M]
    (hμL : ∀ (l : L) (x : M), μ (l • x) = μ x)
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
    (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.levelMulAction c hμL
    ContMDiffConstSMul 𝓘(ℝ, Fin n → ℝ) ∞ L (h.levelSubMulAction c) := by
  let := h.levelSubMulActionChartedSpace c hreg hn
  let := h.levelMulAction c hμL
  have hi := h.isSmoothEmbedding_coe_levelSubMulAction hreg hn
  refine ⟨fun l ↦ hi.contMDiff_iff_comp.2 ?_⟩
  -- The inclusion intertwines the actions on the level and on `M`.
  have hcomp : (Subtype.val : h.levelSubMulAction c → M) ∘ (fun z ↦ l • z) =
      (fun x : M ↦ l • x) ∘ Subtype.val :=
    funext (h.coe_smul_levelMulAction (c := c) hμL l)
  rw [hcomp]
  exact (contMDiff_const_smul l).comp hi.contMDiff

variable (c) in
/-- **The symmetry acts smoothly on a regular level.** If `L` acts smoothly on `M`, its action on
the regular level `μ⁻¹(c)`, with the atlas
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.levelSubMulActionChartedSpace`, is smooth. -/
theorem contMDiffSMul_levelMulAction [TopologicalSpace L] [ChartedSpace HL L]
    [ContMDiffSMul IL I' ∞ L M]
    (hμL : ∀ (l : L) (x : M), μ (l • x) = μ x)
    (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
    (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.levelMulAction c hμL
    ContMDiffSMul IL 𝓘(ℝ, Fin n → ℝ) ∞ L (h.levelSubMulAction c) :=
  letI := h.levelSubMulActionChartedSpace c hreg hn
  letI := h.levelMulAction c hμL
  (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiffSMul contMDiff_id
    (h.coe_smul_levelMulAction (c := c) hμL)

/-! ### The action on the reduced space -/

section Quotient

variable [ProperSMul G M]
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
  (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)
  [SMulCommClass L G M] (hμL : ∀ (l : L) (x : M), μ (l • x) = μ x)

/-- **The symmetry acts smoothly on the reduced space.** A smooth action of `L` on `M` commuting
with that of `G` and preserving `μ` descends to a smooth action `l • [z] = [l • z]` on the reduced
space `μ⁻¹(c) / G_c`, for its atlas
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitRelQuotientChartedSpace`. -/
theorem contMDiffSMul_orbitRelQuotient_levelMulAction [IL.Boundaryless] [TopologicalSpace L]
    [ChartedSpace HL L] [IsManifold IL ∞ L] [ContMDiffSMul IL I' ∞ L M] :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    letI := h.levelMulAction c hμL
    haveI := h.smulCommClass_levelMulAction c hμL
    ContMDiffSMul IL 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)) ∞ L
      (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c)) := by
  let := h.levelMulAction c hμL
  have := h.smulCommClass_levelMulAction c hμL
  exact h.contMDiffSMul_orbitRelQuotient hreg hn d
    (h.contMDiffSMul_levelMulAction (IL := IL) c hμL hreg hn)

/-- **The symmetry acts by smooth maps on the reduced space.** An action of `L` on `M` by smooth
maps commuting with the action of `G` and preserving `μ` descends to an action
`l • [z] = [l • z]` on the reduced space `μ⁻¹(c) / G_c` by smooth maps, for its atlas
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.orbitRelQuotientChartedSpace`. -/
theorem contMDiffConstSMul_orbitRelQuotient_levelMulAction [ContMDiffConstSMul I' ∞ L M] :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    letI := h.levelMulAction c hμL
    haveI := h.smulCommClass_levelMulAction c hμL
    ContMDiffConstSMul 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ)) ∞ L
      (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
        (h.levelSubMulAction c)) := by
  let := h.levelMulAction c hμL
  have := h.smulCommClass_levelMulAction c hμL
  exact h.contMDiffConstSMul_orbitRelQuotient hreg hn d
    (h.contMDiffConstSMul_levelMulAction c hμL hreg hn)

/-- **The symmetry preserves the reduced form.** If `L` acts on `M` by symplectomorphisms
commuting with the action of `G` and preserving `μ`, then every form `η` on the reduced space
`μ⁻¹(c) / G_c` with `π^* η = i^* σ`, such as the reduced symplectic form, is invariant under the
descended action of `L`. -/
theorem mpullback_smul_orbitRelQuotient_eq_self [ContMDiffConstSMul I' ∞ L M]
    (hLσ : ∀ l : L, SmoothForm.mpullback (fun x : M ↦ l • x) (contMDiff_const_smul l) σ = σ) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    letI := h.levelMulAction c hμL
    haveI := h.smulCommClass_levelMulAction c hμL
    haveI := h.contMDiffConstSMul_orbitRelQuotient_levelMulAction hreg hn d hμL
    ∀ {η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c))},
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff σ →
        ∀ l : L, SmoothForm.mpullback (fun q ↦ l • q) (contMDiff_const_smul l) η = η := by
  let := h.levelSubMulActionChartedSpace c hreg hn
  let := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_levelSubMulAction hreg hn
  have := h.isManifold_orbitRelQuotient hreg hn d
  let := h.levelMulAction c hμL
  have := h.smulCommClass_levelMulAction c hμL
  have := h.contMDiffConstSMul_levelMulAction c hμL hreg hn
  have := h.contMDiffConstSMul_orbitRelQuotient_levelMulAction hreg hn d hμL
  intro η hη l
  have hi := (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
  have hl := contMDiff_const_smul (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞)
    (M := h.levelSubMulAction c) l
  refine SmoothForm.mpullback_eq_of_mpullback_eq hi _ hi _ hη hη Quotient.mk_surjective
    (fun z ↦ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).surjective_mfderiv
      (by simp) z) hl ?_ _ rfl
  -- The inclusion intertwines the actions on the level and on `M`, and `L` preserves `σ`.
  have hcomp : (Subtype.val : h.levelSubMulAction c → M) ∘ (fun z ↦ l • z) =
      (fun x : M ↦ l • x) ∘ Subtype.val :=
    funext (h.coe_smul_levelMulAction (c := c) hμL l)
  rw [SmoothForm.mpullback_mpullback]
  simp only [hcomp]
  rw [← SmoothForm.mpullback_mpullback _ _ hi (contMDiff_const_smul l), hLσ l]

end Quotient

end Monoid

/-! ### The reduced moment map -/

section Hamiltonian

variable [ProperSMul G M]
  (hreg : ∀ x, μ x = c → Function.Surjective (h.differential x))
  [IsCancelSMul ((Lie.coadjointRepresentation ℝ I G).stabilizer c) (h.levelSubMulAction c)]
  (hn : finrank ℝ E' - finrank ℝ (GroupLieAlgebra I G) = n)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (d : Lie.EmbeddedLieSubgroupData I ((Lie.coadjointRepresentation ℝ I G).stabilizer c) F)
  [IL.Boundaryless] [CompleteSpace EL] [TopologicalSpace L] [ChartedSpace HL L] [Group L]
  [LieGroup IL ∞ L] [MulAction L M] [ContMDiffSMul IL I' ∞ L M] [SMulCommClass L G M]
  (hμL : ∀ (l : L) (x : M), μ (l • x) = μ x)

/-- **The reduced moment map of a commuting Hamiltonian symmetry.** Let `L` be a Lie group acting
smoothly on `M` by maps commuting with the action of `G` and preserving `μ`, and let `ν : M → 𝔩*`
be a group-level moment map of this action for `σ` which is invariant under the coadjoint
stabilizer `G_c` along the level `μ⁻¹(c)`. If `η` is a form on the reduced space `μ⁻¹(c) / G_c`
with `π^* η = i^* σ`, such as the reduced symplectic form, there is a unique map `ν'` on the
reduced space with `ν' ∘ π = ν ∘ i`, and it is a group-level moment map of the descended action of
`L` for `η`. -/
theorem existsUnique_comp_quotientMk_eq_and_isEquivariantMomentMap
    {ν : M → Module.Dual ℝ (GroupLieAlgebra IL L)} (hν : σ.IsEquivariantMomentMap ν)
    (hνG : ∀ (k : (Lie.coadjointRepresentation ℝ I G).stabilizer c)
      (z : h.levelSubMulAction c), ν (k • (z : M)) = ν z) :
    letI := h.levelSubMulActionChartedSpace c hreg hn
    letI := h.orbitRelQuotientChartedSpace c hreg hn d
    haveI := h.isManifold_levelSubMulAction hreg hn
    haveI := h.isManifold_orbitRelQuotient hreg hn d
    letI := h.levelMulAction c hμL
    haveI := h.smulCommClass_levelMulAction c hμL
    haveI := h.contMDiffSMul_orbitRelQuotient_levelMulAction (IL := IL) hreg hn d hμL
    ∀ {η : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (Fin n → ℝ))
        (MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
          (h.levelSubMulAction c))},
      SmoothForm.mpullback _ (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d).contMDiff η =
          SmoothForm.mpullback Subtype.val
            (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff σ →
        ∃! ν' : MulAction.orbitRel.Quotient ((Lie.coadjointRepresentation ℝ I G).stabilizer c)
            (h.levelSubMulAction c) → Module.Dual ℝ (GroupLieAlgebra IL L),
          ν' ∘ Quotient.mk _ = ν ∘ Subtype.val ∧ η.IsEquivariantMomentMap ν' := by
  let := h.levelSubMulActionChartedSpace c hreg hn
  let := h.orbitRelQuotientChartedSpace c hreg hn d
  have := h.isManifold_levelSubMulAction hreg hn
  have := h.isManifold_orbitRelQuotient hreg hn d
  let := h.levelMulAction c hμL
  have := h.smulCommClass_levelMulAction c hμL
  have := h.contMDiffSMul_levelMulAction (IL := IL) c hμL hreg hn
  have := h.contMDiffSMul_orbitRelQuotient_levelMulAction (IL := IL) hreg hn d hμL
  intro η hη
  exact hν.existsUnique_comp_eq_and_isEquivariantMomentMap
    (h.isSmoothEmbedding_coe_levelSubMulAction hreg hn).contMDiff
    (h.isSubmersion_quotientMk_levelSubMulAction hreg hn d) hη Quotient.mk_surjective
    (h.coe_smul_levelMulAction (c := c) hμL) MulAction.orbitRel.Quotient.smul_mk
    (fun z z' hzz' ↦
      MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hzz'.symm)))
    fun k z ↦ hνG k z

end Hamiltonian

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
