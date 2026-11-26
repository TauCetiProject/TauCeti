/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint.Height.TangentModel
public import TauCeti.Geometry.Lie.Adjoint.Representation.Stabilizer
public import TauCeti.Geometry.Lie.Subgroup.Torus
import TauCeti.Algebra.Lie.Coadjoint
import TauCeti.Geometry.Lie.Subgroup.CartanChart
import TauCeti.Geometry.Lie.Subgroup.Torus.Stabilizer

/-!
# Adjoint stabilizers of torus elements and their root planes

Let `G` be a Lie group with Lie algebra `𝔤` of left-invariant derivations, `B` a separating
invariant form on `𝔤`, and let `𝔤 = t ⊕ E₁ ⊕ ⋯ ⊕ E_r` be a decomposition into an abelian subspace
`t` and root planes `E_i` with roots `α_i ∈ t*` (`TauCeti.IsRootPlaneDecomposition B t α E J`).
For a compact Lie group, a maximal torus `T` with Lie algebra `t = Lie(T)` and an invariant inner
product give such a decomposition
(`TauCeti.Lie.IsMaximalTorus.exists_isInternal_isRootPlane`). This file determines the adjoint
stabilizer `Z_G(X) = {g | Ad_g X = X}` of `X ∈ t` from the roots that vanish at `X`.

* **Its Lie algebra.** The Lie algebra of `Z_G(X)` is the centralizer of `X`
  (`TauCeti.Lie.lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation`), which is `t`
  together with the root planes whose roots vanish at `X`:

  `Lie Z_G(X) = t ⊕ ⨁ {E_i | α_i(X) = 0}`

  (`toSubmodule_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation`). A nonzero
  vector of a root plane lies in it exactly when its root vanishes at `X`
  (`IsRootPlane.mem_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation_iff`), and
  the codimension of `Lie Z_G(X)` in `𝔤` is the total dimension
  `dim (𝔤 ⧸ Lie Z_G(X)) = ∑ {dim E_i | α_i(X) ≠ 0}` of the remaining planes, which is the
  dimension of the orbit `G/Z_G(X)` once that is identified as a manifold
  (`finrank_quotient_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation`).
* **Comparing stabilizers.** When every plane is nonzero, `Lie Z_G(X) ≤ Lie Z_G(Y)` exactly when
  every root vanishing at `X` vanishes at `Y`
  (`lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation_le_iff`). For a compact
  connected group the stabilizers are connected and closed, so they are determined by their Lie
  algebras, and the same holds for the stabilizers themselves:

  `Z_G(X) ≤ Z_G(Y) ↔ ∀ i, α_i(X) = 0 → α_i(Y) = 0`

  (`stabilizer_continuousAdjointRepresentation_le_iff`). Thus the stabilizer `Z_G(X)` itself, not
  just its conjugacy class, is determined by the set of roots vanishing at `X`, the pattern of root
  hyperplanes through `X` (`stabilizer_continuousAdjointRepresentation_eq_stabilizer_iff`).
  Conjugate stabilizers can have different patterns: in `SU(3)`, an element where only `α₁`
  vanishes and one where only `α₂` vanishes have conjugate stabilizers. So stabilizer types, the
  conjugacy classes of stabilizers, correspond to vanishing patterns only up to the Weyl group. On
  a closed Weyl chamber these patterns are its faces; that comparison needs the Weyl group action
  on the roots and is not made here.
* **Regular elements.** If the roots are nonzero, `Lie Z_G(X) = t` exactly when no root vanishes
  at `X` (`toSubmodule_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation_eq_iff`),
  and for a torus `T`, such as a maximal torus, of a compact connected group with `t = Lie(T)`,
  `Z_G(X) = T` exactly when `X` is regular (`stabilizer_continuousAdjointRepresentation_eq_iff`).

Connectedness of `G` is needed for the group statements: in `O(2)`, with `T = SO(2)` and no roots,
the stabilizer of `0` is all of `O(2)`, not `T`.

Unqualified names above and below are in the namespace `TauCeti.IsRootPlaneDecomposition`; names
starting with `IsRootPlane.` are in the namespace `TauCeti`.

## Main results

* `toSubmodule_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation`: the Lie
  algebra of `Z_G(X)` is `t` plus the root planes with `α_i(X) = 0`.
* `finrank_quotient_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation`: the
  codimension of the Lie algebra of `Z_G(X)` in `𝔤`.
* `lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation_le_iff`,
  `stabilizer_continuousAdjointRepresentation_le_iff`,
  `stabilizer_continuousAdjointRepresentation_eq_stabilizer_iff`: the stabilizers of `X, Y ∈ t`
  are compared by the roots vanishing at `X` and `Y`.
* `stabilizer_continuousAdjointRepresentation_eq_iff`: the stabilizer of `X` is the torus exactly
  when `X` is regular.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter V, § 2.
* M. M. Alexandrino and R. G. Bettiol, *Lie Groups and Geometric Aspects of Isometric Actions*,
  Springer, 2015, Lemma 4.26 and Theorem 4.31.
-/

public section

noncomputable section

open Module (Dual finrank)
open scoped ContDiff Manifold

namespace TauCeti

open Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]
  {B : LinearMap.BilinForm ℝ (LeftInvariantDerivation I G)}
  {t : Submodule ℝ (LeftInvariantDerivation I G)}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-! ### A single root plane -/

namespace IsRootPlane

variable {α : Dual ℝ t} {V : Submodule ℝ (LeftInvariantDerivation I G)} {J : Module.End ℝ V}

/-- **Root planes in the Lie algebra of the stabilizer.** A vector `v` of a root plane `E` with
root `α` lies in the Lie algebra of the adjoint stabilizer of `X ∈ t` exactly when `α(X) = 0` or
`v = 0`. -/
theorem mem_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation_iff
    (h : IsRootPlane B t α V J) (X : t) (v : V) :
    (v : LeftInvariantDerivation I G) ∈ lieSubalgebraOfSubgroup (I := I)
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G)) ↔ α X = 0 ∨ v = 0 := by
  rw [lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation, mem_lieAnnihilator,
    ← lie_skew, neg_eq_zero, h.lie_eq_zero_iff]

/-- A nonzero root plane `E` with root `α` lies in the Lie algebra of the adjoint stabilizer of
`X ∈ t` exactly when `α(X) = 0`. -/
theorem le_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation_iff
    (h : IsRootPlane B t α V J) (X : t) (hV : V ≠ ⊥) :
    V ≤ (lieSubalgebraOfSubgroup (I := I)
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G))).toSubmodule ↔ α X = 0 := by
  refine ⟨fun hle ↦ ?_, fun hα v hv ↦ ?_⟩
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
    have hmem := h.mem_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation_iff X
      ⟨v, hv⟩
    exact (hmem.1 (hle hv)).resolve_right (by simpa using hv0)
  · exact (h.mem_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation_iff X
      ⟨v, hv⟩).2 (Or.inl hα)

end IsRootPlane

namespace IsRootPlaneDecomposition

variable {ι : Type*} [Finite ι] {α : ι → Dual ℝ t}
  {V : ι → Submodule ℝ (LeftInvariantDerivation I G)} {J : (i : ι) → Module.End ℝ (V i)}

/-! ### The Lie algebra of the stabilizer -/

omit [Finite ι] in
/-- **The Lie algebra of the adjoint stabilizer of a torus element.** For a separating invariant
form and `X ∈ t`, the Lie algebra of `Z_G(X) = {g | Ad_g X = X}` is `t` together with the root
planes whose roots vanish at `X`. -/
theorem toSubmodule_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation [Fintype ι]
    (hD : IsRootPlaneDecomposition B t α V J) (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (hsep : B.SeparatingLeft) (X : t) :
    (lieSubalgebraOfSubgroup (I := I)
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G))).toSubmodule =
      t ⊔ ⨆ i ∈ ({i | α i X = 0} : Finset ι), V i := by
  rw [lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation,
    ← lieAnnihilator_bilinForm_apply_eq_of_lieInvariant hB hsep, hD.lieAnnihilator_eq hB hsep X]

omit [Finite ι] in
/-- **The codimension of the Lie algebra of the stabilizer of a torus element.** For a separating
invariant form and `X ∈ t`, the quotient of `𝔤` by the Lie algebra of `Z_G(X)` has dimension
`∑ {dim E_i | α_i(X) ≠ 0}`. This is the dimension of the orbit `G/Z_G(X)` once that is identified
as a manifold, which is not done here. -/
theorem finrank_quotient_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation
    [Fintype ι] (hD : IsRootPlaneDecomposition B t α V J)
    (hB : B.lieInvariant (LeftInvariantDerivation I G)) (hsep : B.SeparatingLeft) (X : t) :
    finrank ℝ (LeftInvariantDerivation I G ⧸ (lieSubalgebraOfSubgroup (I := I)
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G))).toSubmodule) =
      ∑ i with α i X ≠ 0, finrank ℝ (V i) := by
  have : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  rw [lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation,
    ← lieAnnihilator_bilinForm_apply_eq_of_lieInvariant hB hsep,
    hD.finrank_quotient_lieAnnihilator hB hsep X]

/-! ### Comparing stabilizers -/

/-- **Comparing stabilizers in the Lie algebra.** For a separating invariant form whose root planes
are nonzero and `X, Y ∈ t`, the Lie algebra of `Z_G(X)` lies in that of `Z_G(Y)` exactly when
every root vanishing at `X` vanishes at `Y`. -/
theorem lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation_le_iff
    (hD : IsRootPlaneDecomposition B t α V J)
    (hB : B.lieInvariant (LeftInvariantDerivation I G)) (hsep : B.SeparatingLeft)
    (hV : ∀ i, V i ≠ ⊥) (X Y : t) :
    lieSubalgebraOfSubgroup (I := I)
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G)) ≤
      lieSubalgebraOfSubgroup (I := I)
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (Y : LeftInvariantDerivation I G)) ↔
      ∀ i, α i X = 0 → α i Y = 0 := by
  classical
  have := Fintype.ofFinite ι
  rw [← LieSubalgebra.toSubmodule_le_toSubmodule,
    hD.toSubmodule_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation hB hsep X]
  refine ⟨fun h i hi ↦ ?_, fun h ↦ ?_⟩
  · refine (IsRootPlane.le_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation_iff
      (hD.isRootPlane i) Y (hV i)).1 (le_trans ?_ h)
    exact le_sup_of_le_right (le_iSup₂_of_le i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)
      le_rfl)
  · rw [hD.toSubmodule_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation hB hsep Y]
    refine sup_le_sup_left (iSup₂_le fun i hi ↦ ?_) t
    exact le_iSup₂_of_le i (Finset.mem_filter.2 ⟨Finset.mem_univ i,
      h i (Finset.mem_filter.1 hi).2⟩) le_rfl

section Compact

variable [CompactSpace G] [ConnectedSpace G]

/-- **Comparing the stabilizers of a compact connected group.** For a separating invariant form
whose root planes are nonzero and `X, Y ∈ t`, the adjoint stabilizer `Z_G(X)` lies in `Z_G(Y)`
exactly when every root vanishing at `X` vanishes at `Y`. The stabilizers are closed and connected,
so each is determined by its Lie algebra. -/
theorem stabilizer_continuousAdjointRepresentation_le_iff
    (hD : IsRootPlaneDecomposition B t α V J)
    (hB : B.lieInvariant (LeftInvariantDerivation I G)) (hsep : B.SeparatingLeft)
    (hV : ∀ i, V i ≠ ⊥) (X Y : t) :
    (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
        (X : LeftInvariantDerivation I G) ≤
      (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
        (Y : LeftInvariantDerivation I G) ↔
      ∀ i, α i X = 0 → α i Y = 0 := by
  rw [← hD.lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation_le_iff hB hsep hV]
  exact ⟨lieSubalgebraOfSubgroup_mono, le_of_lieSubalgebraOfSubgroup_le
    (isClosed_stabilizer_continuousAdjointRepresentation _)
    (isConnected_stabilizer_continuousAdjointRepresentation _).isPreconnected
    (isClosed_stabilizer_continuousAdjointRepresentation _)⟩

/-- **Equal adjoint stabilizers have equal root vanishing patterns.** For a compact connected
group, a separating invariant form whose root planes are nonzero and `X, Y ∈ t`, the adjoint
stabilizers of `X` and `Y` agree exactly when the same roots vanish at `X` and at `Y`. This is
equality of the stabilizers, not of their conjugacy classes: stabilizer types correspond to
vanishing patterns only up to the Weyl group. -/
theorem stabilizer_continuousAdjointRepresentation_eq_stabilizer_iff
    (hD : IsRootPlaneDecomposition B t α V J)
    (hB : B.lieInvariant (LeftInvariantDerivation I G)) (hsep : B.SeparatingLeft)
    (hV : ∀ i, V i ≠ ⊥) (X Y : t) :
    (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
        (X : LeftInvariantDerivation I G) =
      (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
        (Y : LeftInvariantDerivation I G) ↔
      ∀ i, α i X = 0 ↔ α i Y = 0 := by
  rw [le_antisymm_iff, hD.stabilizer_continuousAdjointRepresentation_le_iff hB hsep hV,
    hD.stabilizer_continuousAdjointRepresentation_le_iff hB hsep hV]
  exact ⟨fun h i ↦ ⟨h.1 i, h.2 i⟩, fun h ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩⟩

end Compact

/-! ### Regular elements -/

/-- **The stabilizer of a regular element.** For a separating invariant form whose roots and root
planes are nonzero and `X ∈ t`, the Lie algebra of `Z_G(X)` is `t` exactly when no root vanishes
at `X`. -/
theorem toSubmodule_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation_eq_iff
    (hD : IsRootPlaneDecomposition B t α V J) (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (hsep : B.SeparatingLeft) (hα : ∀ i, α i ≠ 0) (hV : ∀ i, V i ≠ ⊥) (X : t) :
    (lieSubalgebraOfSubgroup (I := I)
        ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
          (X : LeftInvariantDerivation I G))).toSubmodule = t ↔ ∀ i, α i X ≠ 0 := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun h i hi ↦ hα i ?_, fun h ↦ ?_⟩
  · -- A nonzero vector of `E_i` would lie in the abelian subspace `t`, so `α_i` would vanish.
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hV i)
    have hle :=
      (IsRootPlane.le_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation_iff
        (hD.isRootPlane i) X (hV i)).2 hi
    have hvt : v ∈ t := h ▸ hle hv
    ext H
    refine (((hD.isRootPlane i).lie_eq_zero_iff H ⟨v, hv⟩).1
      (hD.lie_eq_zero H.property hvt)).resolve_right ?_
    simpa using hv0
  · rw [hD.toSubmodule_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation hB hsep X]
    simp [h]

/-- **The stabilizer of a regular element is the torus.** Let `T` be a torus of a compact connected
Lie group, for instance a maximal torus, and decompose the Lie algebra into `t = Lie(T)` and
nonzero root planes with nonzero roots, for a separating invariant form. Then `X ∈ t` has adjoint
stabilizer `Z_G(X) = T` exactly when no root vanishes at `X`. -/
theorem stabilizer_continuousAdjointRepresentation_eq_iff [CompactSpace G] [ConnectedSpace G]
    {T : Subgroup G} (hT : IsTorus T) (ht : (lieSubalgebraOfSubgroup (I := I) T).toSubmodule = t)
    (hD : IsRootPlaneDecomposition B t α V J) (hB : B.lieInvariant (LeftInvariantDerivation I G))
    (hsep : B.SeparatingLeft) (hα : ∀ i, α i ≠ 0) (hV : ∀ i, V i ≠ ⊥) (X : t) :
    (continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.stabilizer
        (X : LeftInvariantDerivation I G) = T ↔ ∀ i, α i X ≠ 0 := by
  subst ht
  have := hT.isMulCommutative
  have hTc : IsClosed (T : Set G) := hT.isCompact.isClosed
  rw [← hD.toSubmodule_lieSubalgebraOfSubgroup_stabilizer_continuousAdjointRepresentation_eq_iff
    hB hsep hα hV, LieSubalgebra.toSubmodule_inj]
  refine ⟨fun h ↦ by rw [h], fun h ↦ le_antisymm ?_
    (le_stabilizer_continuousAdjointRepresentation X.property)⟩
  exact le_of_lieSubalgebraOfSubgroup_le (isClosed_stabilizer_continuousAdjointRepresentation _)
    (isConnected_stabilizer_continuousAdjointRepresentation _).isPreconnected hTc h.le

end IsRootPlaneDecomposition

end TauCeti
