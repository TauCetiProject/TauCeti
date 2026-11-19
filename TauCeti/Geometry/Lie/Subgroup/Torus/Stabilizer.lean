/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Stabilizer
public import TauCeti.Geometry.Lie.Subgroup.OneParameter
import TauCeti.Geometry.Lie.Adjoint.Derivation
import TauCeti.Geometry.Lie.Adjoint.InvariantForm
import TauCeti.Geometry.Lie.Adjoint.Representation.Stabilizer
import TauCeti.Geometry.Lie.Subgroup.Torus.Centralizer

/-!
# Connected adjoint and coadjoint stabilizers of compact connected Lie groups

Let `G` be a compact connected finite-dimensional real Lie group with Lie algebra `𝔤`. This file
proves that the stabilizer `Z_G(ξ) = {g | Ad_g ξ = ξ}` of every `ξ ∈ 𝔤` under the adjoint
representation is connected, and so is the stabilizer `G_ν = {g | Ad*_g ν = ν}` of every `ν ∈ 𝔤*`
under the coadjoint representation. These are the isotropy groups of the adjoint and coadjoint
orbits, which are therefore homogeneous spaces `G / Z_G(ξ)` and `G / G_ν` with connected isotropy.

For any Lie group, `Z_G(ξ)` is the centralizer of the closure `T_ξ` of the one-parameter subgroup
`t ↦ exp (t ξ)` (`TauCeti.Lie.closedOneParameterSubgroup`): an element commuting with every
`exp (t ξ)` commutes with their closure, since centralizers are closed
(`TauCeti.Lie.stabilizer_adjointRepresentation_eq_centralizer_closedOneParameterSubgroup`). In a
compact group `T_ξ` is a torus, and the centralizer of a torus in a compact connected Lie group is
connected (`TauCeti.Lie.IsTorus.isConnected_centralizer`).

For the coadjoint stabilizer, an `Ad`-invariant inner product `b` on `𝔤` identifies `𝔤` with `𝔤*`
equivariantly, so that `G_ν` is the adjoint stabilizer of the element `X` with `ν = b(X, ·)`
(`TauCeti.Lie.stabilizer_coadjointRepresentation_eq_stabilizer_adjointRepresentation`,
`TauCeti.Lie.exists_stabilizer_coadjointRepresentation_eq`).

Connectedness of `G` is needed: in `O(2)` the stabilizer of `0 ∈ 𝔰𝔬(2)` is all of `O(2)`. The
statement is special to elements of the Lie algebra: in `SO(3)` the centralizer of the group
element `diag(1, -1, -1)` is a copy of `O(2)`, which is disconnected.

## Main results

* `TauCeti.Lie.stabilizer_adjointRepresentation_eq_centralizer_closedOneParameterSubgroup`:
  `Z_G(ξ)` is the centralizer of `T_ξ`.
* `TauCeti.Lie.exists_stabilizer_coadjointRepresentation_eq`: for compact `G`, every coadjoint
  stabilizer is an adjoint stabilizer.
* `TauCeti.Lie.isConnected_stabilizer_adjointRepresentation`: `Z_G(ξ)` is connected.
* `TauCeti.Lie.isConnected_stabilizer_coadjointRepresentation`: `G_ν` is connected.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter IV, § 2.
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **The adjoint stabilizer is the centralizer of a closed one-parameter subgroup.** An element
`g` fixes `ξ` under the adjoint representation exactly when it commutes with the closure `T_ξ` of
the one-parameter subgroup `t ↦ exp (t ξ)`. -/
theorem stabilizer_adjointRepresentation_eq_centralizer_closedOneParameterSubgroup
    [IsTopologicalGroup G] (ξ : GroupLieAlgebra I G) :
    (adjointRepresentation ℝ I G).stabilizer ξ =
      Subgroup.centralizer (closedOneParameterSubgroup ξ : Set G) := by
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra (I := I) (G := G)
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  have hexp (t : ℝ) : lieExp (I := I) (t • e.symm ξ) = mulInvariantExp (t • ξ) := by
    rw [lieExp_eq_mulInvariantExp, map_smul, ← leftInvariantDerivationLieEquivGroupLieAlgebra_apply,
      LieEquiv.apply_symm_apply]
  have he (g : G) (D : LeftInvariantDerivation I G) :
      e (Ad (I := I) g D) = tangentAd (I := I) g (e D) :=
    leftInvariantDerivationLieEquivGroupLieAlgebra_Ad g D
  -- Through the identification of the Lie algebra with left-invariant derivations, this is the
  -- centralizer of the one-parameter subgroup itself; a centralizer is closed, so it is also the
  -- centralizer of the closure.
  have hstab : (adjointRepresentation ℝ I G).stabilizer ξ =
      (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
        (e.symm ξ) := by
    ext g
    rw [Representation.mem_stabilizer, adjointRepresentation_apply,
      mem_stabilizer_continuousAdjointRepresentation_iff, ← EmbeddingLike.apply_eq_iff_eq e, he,
      LieEquiv.apply_symm_apply, tangentAd_apply]
  rw [hstab, stabilizer_continuousAdjointRepresentation_eq_centralizer]
  refine le_antisymm (fun g hg ↦ ?_) (Subgroup.centralizer_le ?_)
  · have hle : closedOneParameterSubgroup ξ ≤ Subgroup.centralizer {g} :=
      (closedOneParameterSubgroup_le (Set.isClosed_centralizer _)).2 fun t ↦ by
        have h : lieExp (I := I) (t • e.symm ξ) * g = g * lieExp (I := I) (t • e.symm ξ) :=
          Subgroup.mem_centralizer_iff.1 hg _ ⟨t, rfl⟩
        rw [hexp] at h
        exact Subgroup.mem_centralizer_singleton_iff.2 h
    exact Subgroup.mem_centralizer_iff.2 fun k hk ↦
      Subgroup.mem_centralizer_singleton_iff.1 (hle hk)
  · rintro _ ⟨t, rfl⟩
    simp only [SetLike.mem_coe, hexp, mulInvariantExp_smul_mem_closedOneParameterSubgroup]

variable [CompactSpace G]

omit [T2Space G] in
/-- **Coadjoint stabilizers of compact Lie groups are adjoint stabilizers.** For a compact
finite-dimensional real Lie group, every coadjoint stabilizer `G_ν` is the adjoint stabilizer of
some element of the Lie algebra: the one corresponding to `ν` under an `Ad`-invariant inner
product. -/
theorem exists_stabilizer_coadjointRepresentation_eq
    (ν : Module.Dual ℝ (GroupLieAlgebra I G)) :
    ∃ X : GroupLieAlgebra I G, (coadjointRepresentation ℝ I G).stabilizer ν =
      (adjointRepresentation ℝ I G).stabilizer X := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  obtain ⟨b, hsymm, hpos, hinv⟩ :=
    exists_isSymm_posDef_continuousBilinearMap_adjoint_invariant (I := I) (G := G)
  have hb (a : GroupLieAlgebra I G) (ha : ∀ c, b a c = 0) : a = 0 := by
    by_contra h
    exact (hpos a h).ne' (ha a)
  -- The invariant inner product identifies the Lie algebra with its dual.
  let B : LinearMap.BilinForm ℝ (GroupLieAlgebra I G) := b.toLinearMap₁₂
  have hB : B.Nondegenerate := ⟨hb, fun a ha ↦ hb a fun c ↦ (hsymm a c).trans (ha c)⟩
  refine ⟨(B.toDual hB).symm ν, ?_⟩
  have hν : (b ((B.toDual hB).symm ν) : Module.Dual ℝ (GroupLieAlgebra I G)) = ν :=
    LinearMap.ext fun c ↦ LinearMap.congr_fun ((B.toDual hB).apply_symm_apply ν) c
  rw [← stabilizer_coadjointRepresentation_eq_stabilizer_adjointRepresentation hb hinv, hν]

omit [T2Space G] in
/-- **Adjoint stabilizers are connected.** In a compact connected finite-dimensional real Lie
group, the stabilizer `{g | Ad_g ξ = ξ}` of each `ξ` in the Lie algebra is connected. -/
theorem isConnected_stabilizer_adjointRepresentation [ConnectedSpace G]
    (ξ : GroupLieAlgebra I G) :
    IsConnected ((adjointRepresentation ℝ I G).stabilizer ξ : Set G) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  rw [stabilizer_adjointRepresentation_eq_centralizer_closedOneParameterSubgroup]
  exact (isTorus_closedOneParameterSubgroup ξ).isConnected_centralizer I

omit [T2Space G] in
/-- **Coadjoint stabilizers are connected.** In a compact connected finite-dimensional real Lie
group, the coadjoint stabilizer `G_ν = {g | Ad*_g ν = ν}` of each `ν` in the dual of the Lie
algebra is connected. -/
theorem isConnected_stabilizer_coadjointRepresentation [ConnectedSpace G]
    (ν : Module.Dual ℝ (GroupLieAlgebra I G)) :
    IsConnected ((coadjointRepresentation ℝ I G).stabilizer ν : Set G) := by
  obtain ⟨X, hX⟩ := exists_stabilizer_coadjointRepresentation_eq ν
  rw [hX]
  exact isConnected_stabilizer_adjointRepresentation X

end TauCeti.Lie
