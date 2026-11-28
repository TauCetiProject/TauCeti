/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.BlockSucc
public import TauCeti.Topology.Algebra.OrthogonalGroup
public import TauCeti.Topology.Algebra.SequentialColimitGroup
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

/-!
# Stable orthogonal and special orthogonal groups

Placing an `n × n` orthogonal or special orthogonal matrix in the upper-left block and extending
with `1` on the diagonal (`TauCeti.continuousOrthogonalBlockSucc ℝ` and
`TauCeti.continuousSpecialOrthogonalBlockSucc ℝ`) gives sequential diagrams of compact Hausdorff
topological groups indexed by `ℕ`, whose transitions are closed embeddings.

Specializing `TauCeti.SequentialColimitGroup` to these two diagrams yields:
* `TauCeti.StableOrthogonalGroup` (`O`), the sequential colimit of
  `O(n) := Matrix.orthogonalGroup (Fin n) ℝ`;
* `TauCeti.StableSpecialOrthogonalGroup` (`SO`), the sequential colimit of
  `SO(n) := Matrix.specialOrthogonalGroup (Fin n) ℝ`.

Both stable groups inherit `IsTopologicalGroup`, `T4Space`, closed-embedding stage inclusions
(`TauCeti.SequentialColimitGroup.of`), and universal properties for continuous maps
(`liftContinuous`) and continuous homomorphisms (`lift`) from `TauCeti.SequentialColimitGroup`.
The finite-stage determinant sign `TauCeti.orthogonalDetSign` descends to a continuous homomorphism
`TauCeti.StableOrthogonalGroup.det : StableOrthogonalGroup →ₜ* ℤˣ`, classifying path components
(`TauCeti.StableOrthogonalGroup.joined_iff_det_eq`), and `toStableOrthogonalGroup : SO →ₜ* O` is
both a closed and an open embedding onto `det.ker`. Connectivity and homotopy-group stability for
`O` and `SO` are proved in `TauCeti.Topology.Algebra.StableOrthogonalGroup.Stability`.

## Main definitions

* `TauCeti.StableOrthogonalGroup`, `TauCeti.StableSpecialOrthogonalGroup`: the stable orthogonal
  and special orthogonal groups `O` and `SO`.
* `TauCeti.StableOrthogonalGroup.det`: the continuous determinant homomorphism `O →ₜ* ℤˣ`.
* `TauCeti.StableSpecialOrthogonalGroup.toStableOrthogonalGroup`: the inclusion `SO →ₜ* O`.

## Main results

* `TauCeti.StableSpecialOrthogonalGroup.isClosedEmbedding_toStableOrthogonalGroup`,
  `TauCeti.StableSpecialOrthogonalGroup.isOpenEmbedding_toStableOrthogonalGroup`: `SO → O` is both
  a closed and an open embedding with image `det.ker`.
* `TauCeti.StableOrthogonalGroup.joined_iff_det_eq`: path components of `O` are classified by
  determinant.
-/

public section

noncomputable section

open Topology Set

namespace TauCeti

attribute [local instance] starRingOfComm

/-! ### The stable orthogonal group `O` -/

/-- **The stable orthogonal group `O`**: the sequential colimit of the real matrix orthogonal
groups `O(n)` along the block inclusions `A ↦ diag(A, 1)`, equipped with the sequential colimit
topology (which is `T4`, compactly generated, and makes multiplication and inversion jointly
continuous). -/
abbrev StableOrthogonalGroup : Type :=
  SequentialColimitGroup (continuousOrthogonalBlockSucc ℝ)

namespace StableOrthogonalGroup

instance instIsTopologicalGroup : IsTopologicalGroup StableOrthogonalGroup :=
  SequentialColimitGroup.isTopologicalGroup (continuousOrthogonalBlockSucc ℝ)
    (isClosedEmbedding_continuousOrthogonalBlockSucc ℝ)

instance instT4Space : T4Space StableOrthogonalGroup :=
  SequentialColimitGroup.t4Space (continuousOrthogonalBlockSucc ℝ)
    (isClosedEmbedding_continuousOrthogonalBlockSucc ℝ)

/-- The determinant on `O`, taking values in `ℤˣ = {±1}` (with the discrete topology). -/
def det : StableOrthogonalGroup →ₜ* ℤˣ :=
  SequentialColimitGroup.lift (continuousOrthogonalBlockSucc ℝ)
    (fun n ↦ ⟨orthogonalDetSign (Fin n) ℝ, continuous_orthogonalDetSign⟩)
    (fun n A ↦ by
      -- Unfold the `ContinuousMonoidHom` wrapper `{ toMonoidHom := orthogonalDetSign, ... }`.
      change orthogonalDetSign (Fin (n + 1)) ℝ (continuousOrthogonalBlockSucc ℝ n A) =
        orthogonalDetSign (Fin n) ℝ A
      rw [orthogonalDetSign_apply, orthogonalDetSign_apply,
        continuousOrthogonalBlockSucc_apply, coe_orthogonalBlockSucc, Matrix.det_blockSucc])

open Classical in
/-- Evaluating `StableOrthogonalGroup.det` on a stage matrix `of n A` returns `1` or `-1`
according to `(A : Matrix (Fin n) (Fin n) ℝ).det = 1`. -/
@[simp]
theorem det_of (n : ℕ) (A : Matrix.orthogonalGroup (Fin n) ℝ) :
    det (SequentialColimitGroup.of (continuousOrthogonalBlockSucc ℝ) n A) =
      if (A : Matrix (Fin n) (Fin n) ℝ).det = 1 then 1 else -1 := by
  rw [det, SequentialColimitGroup.lift_of]
  exact orthogonalDetSign_apply A

/-- Coerced to `ℝ`, `StableOrthogonalGroup.det` agrees on every stage `O(n)` with the matrix
determinant. -/
theorem coe_det_of (n : ℕ) (A : Matrix.orthogonalGroup (Fin n) ℝ) :
    ((det (SequentialColimitGroup.of (continuousOrthogonalBlockSucc ℝ) n A) : ℤ) : ℝ) =
      (A : Matrix (Fin n) (Fin n) ℝ).det := by
  rw [det_of]
  rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup A.property with hA | hA <;>
    simp [hA, show (-1 : ℝ) ≠ 1 by norm_num]

/-- A finite-stage orthogonal matrix has `det (of n A) = 1` in `O` if and only if its matrix
determinant is `1`. -/
theorem det_of_eq_one_iff (n : ℕ) (A : Matrix.orthogonalGroup (Fin n) ℝ) :
    det (SequentialColimitGroup.of (continuousOrthogonalBlockSucc ℝ) n A) = 1 ↔
      (A : Matrix (Fin n) (Fin n) ℝ).det = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have hc := coe_det_of n A
  rw [show (det (SequentialColimitGroup.of (continuousOrthogonalBlockSucc ℝ) n A) : ℤ) = 1 from
    congrArg Units.val h] at hc
  simpa using hc.symm

end StableOrthogonalGroup

/-! ### The stable special orthogonal group `SO` -/

/-- **The stable special orthogonal group `SO`**: the sequential colimit of the real special
orthogonal groups `SO(n)` along the block inclusions `A ↦ diag(A, 1)`. -/
abbrev StableSpecialOrthogonalGroup : Type :=
  SequentialColimitGroup (continuousSpecialOrthogonalBlockSucc ℝ)

namespace StableSpecialOrthogonalGroup

instance instIsTopologicalGroup : IsTopologicalGroup StableSpecialOrthogonalGroup :=
  SequentialColimitGroup.isTopologicalGroup (continuousSpecialOrthogonalBlockSucc ℝ)
    (isClosedEmbedding_continuousSpecialOrthogonalBlockSucc ℝ)

instance instT4Space : T4Space StableSpecialOrthogonalGroup :=
  SequentialColimitGroup.t4Space (continuousSpecialOrthogonalBlockSucc ℝ)
    (isClosedEmbedding_continuousSpecialOrthogonalBlockSucc ℝ)

/-- **The stable special orthogonal group is path-connected.** -/
instance instPathConnectedSpace : PathConnectedSpace StableSpecialOrthogonalGroup := by
  refine ⟨⟨1⟩, fun x y ↦ ?_⟩
  obtain ⟨n, A, B, rfl, rfl⟩ :=
    SequentialColimitGroup.exists_of₂ (continuousSpecialOrthogonalBlockSucc ℝ) x y
  exact (PathConnectedSpace.joined A B).map
    (SequentialColimitGroup.of (continuousSpecialOrthogonalBlockSucc ℝ) n).continuous

/-- The canonical inclusion `SO →ₜ* O`, induced by `SO(n) →* O(n)`. -/
def toStableOrthogonalGroup : StableSpecialOrthogonalGroup →ₜ* StableOrthogonalGroup :=
  SequentialColimitGroup.lift (continuousSpecialOrthogonalBlockSucc ℝ)
    (fun n ↦ (SequentialColimitGroup.of (continuousOrthogonalBlockSucc ℝ) n).comp
      ⟨Matrix.specialOrthogonalGroup.toOrthogonalGroup,
        Matrix.specialOrthogonalGroup.continuous_toOrthogonalGroup⟩)
    (fun n A ↦ by
      -- Unfold `ContinuousMonoidHom.comp` and the `continuous_toOrthogonalGroup` wrapper.
      change SequentialColimitGroup.of (continuousOrthogonalBlockSucc ℝ) (n + 1)
          (Matrix.specialOrthogonalGroup.toOrthogonalGroup
            (continuousSpecialOrthogonalBlockSucc ℝ n A)) =
        SequentialColimitGroup.of (continuousOrthogonalBlockSucc ℝ) n
          (Matrix.specialOrthogonalGroup.toOrthogonalGroup A)
      rw [continuousSpecialOrthogonalBlockSucc_apply, toOrthogonalGroup_specialOrthogonalBlockSucc,
        ← continuousOrthogonalBlockSucc_apply]
      exact SequentialColimitGroup.of_succ (continuousOrthogonalBlockSucc ℝ) n _)

/-- On a finite stage `SO(n)`, `toStableOrthogonalGroup` agrees with the stage inclusion
`SO(n) → O(n) → O`. -/
@[simp]
theorem toStableOrthogonalGroup_of (n : ℕ) (A : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    toStableOrthogonalGroup
        (SequentialColimitGroup.of (continuousSpecialOrthogonalBlockSucc ℝ) n A) =
      SequentialColimitGroup.of (continuousOrthogonalBlockSucc ℝ) n
        (Matrix.specialOrthogonalGroup.toOrthogonalGroup A) := by
  rw [toStableOrthogonalGroup, SequentialColimitGroup.lift_of, ContinuousMonoidHom.coe_comp,
    Function.comp_apply]
  -- Unfold the `ContinuousMonoidHom` wrapper `{ toMonoidHom := toOrthogonalGroup, ... }`.
  rfl

/-- The canonical inclusion `SO → O` is injective. -/
theorem toStableOrthogonalGroup_injective : Function.Injective toStableOrthogonalGroup := by
  intro x y hxy
  obtain ⟨n, A, B, rfl, rfl⟩ :=
    SequentialColimitGroup.exists_of₂ (continuousSpecialOrthogonalBlockSucc ℝ) x y
  simp only [toStableOrthogonalGroup_of] at hxy
  have h1 := SequentialColimitGroup.of_injective (continuousOrthogonalBlockSucc ℝ)
    (fun k ↦ (isClosedEmbedding_continuousOrthogonalBlockSucc ℝ k).injective) n hxy
  exact congrArg (SequentialColimitGroup.of (continuousSpecialOrthogonalBlockSucc ℝ) n)
    (Matrix.specialOrthogonalGroup.isClosedEmbedding_toOrthogonalGroup.injective h1)

/-- The image of `toStableOrthogonalGroup` has determinant `1`. -/
@[simp]
theorem det_toStableOrthogonalGroup (x : StableSpecialOrthogonalGroup) :
    StableOrthogonalGroup.det (toStableOrthogonalGroup x) = 1 := by
  obtain ⟨n, A, rfl⟩ :=
    SequentialColimitGroup.exists_of (continuousSpecialOrthogonalBlockSucc ℝ) x
  rw [toStableOrthogonalGroup_of, StableOrthogonalGroup.det_of,
    Matrix.specialOrthogonalGroup.coe_toOrthogonalGroup,
    (Matrix.mem_specialOrthogonalGroup_iff.1 A.property).2]
  simp

/-- The image of `SO → O` is the kernel of `StableOrthogonalGroup.det`. -/
theorem range_toStableOrthogonalGroup :
    Set.range toStableOrthogonalGroup =
      (StableOrthogonalGroup.det : StableOrthogonalGroup →* ℤˣ).ker := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact det_toStableOrthogonalGroup x
  · intro hy
    obtain ⟨n, B, rfl⟩ :=
      SequentialColimitGroup.exists_of (continuousOrthogonalBlockSucc ℝ) y
    have hdet := (StableOrthogonalGroup.det_of_eq_one_iff n B).1 hy
    refine ⟨SequentialColimitGroup.of (continuousSpecialOrthogonalBlockSucc ℝ) n
      ⟨B, B.property, hdet⟩, ?_⟩
    rw [toStableOrthogonalGroup_of]
    congr 1
    exact Subtype.ext (Matrix.specialOrthogonalGroup.coe_toOrthogonalGroup _)

/-- `SO → O` is a closed embedding. -/
theorem isClosedEmbedding_toStableOrthogonalGroup :
    IsClosedEmbedding toStableOrthogonalGroup := by
  refine .of_continuous_injective_isClosedMap toStableOrthogonalGroup.continuous
    toStableOrthogonalGroup_injective fun Z hZ ↦ ?_
  rw [SequentialColimitGroup.isClosed_iff]
  intro n
  have hpre : (SequentialColimitGroup.of (continuousOrthogonalBlockSucc ℝ) n ⁻¹'
        (toStableOrthogonalGroup '' Z) : Set (Matrix.orthogonalGroup (Fin n) ℝ)) =
      Matrix.specialOrthogonalGroup.toOrthogonalGroup ''
        (SequentialColimitGroup.of (continuousSpecialOrthogonalBlockSucc ℝ) n ⁻¹' Z) := by
    ext (B : Matrix.orthogonalGroup (Fin n) ℝ)
    constructor
    · rintro ⟨x, hxZ, hxB⟩
      have hdet := (StableOrthogonalGroup.det_of_eq_one_iff n B).1
        (hxB ▸ det_toStableOrthogonalGroup x)
      let B' : Matrix.specialOrthogonalGroup (Fin n) ℝ := ⟨B, B.property, hdet⟩
      have hB' : toStableOrthogonalGroup
          (SequentialColimitGroup.of (continuousSpecialOrthogonalBlockSucc ℝ) n B') =
          toStableOrthogonalGroup x := by
        rw [toStableOrthogonalGroup_of,
          show Matrix.specialOrthogonalGroup.toOrthogonalGroup B' = B from
            Subtype.ext (Matrix.specialOrthogonalGroup.coe_toOrthogonalGroup B'), hxB]
      have hxeq := toStableOrthogonalGroup_injective hB'
      exact ⟨B', by simpa [hxeq] using hxZ,
        Subtype.ext (Matrix.specialOrthogonalGroup.coe_toOrthogonalGroup B')⟩
    · rintro ⟨B', hB', rfl⟩
      exact ⟨SequentialColimitGroup.of (continuousSpecialOrthogonalBlockSucc ℝ) n B', hB',
        toStableOrthogonalGroup_of n B'⟩
  rw [hpre]
  exact Matrix.specialOrthogonalGroup.isClosedEmbedding_toOrthogonalGroup.isClosedMap _
    (hZ.preimage (SequentialColimitGroup.of
      (continuousSpecialOrthogonalBlockSucc ℝ) n).continuous)

/-- `SO → O` is an open embedding (its image is the clopen kernel of `det`). -/
theorem isOpenEmbedding_toStableOrthogonalGroup :
    IsOpenEmbedding toStableOrthogonalGroup := by
  refine (isOpenEmbedding_iff _).2 ⟨isClosedEmbedding_toStableOrthogonalGroup.isEmbedding, ?_⟩
  rw [range_toStableOrthogonalGroup]
  exact (isOpen_discrete ({1} : Set ℤˣ)).preimage StableOrthogonalGroup.det.continuous

end StableSpecialOrthogonalGroup

namespace StableOrthogonalGroup

/-- **Path components of `O`**: two points in the stable orthogonal group are joined by a path
exactly when they have the same determinant. -/
theorem joined_iff_det_eq {x y : StableOrthogonalGroup} : Joined x y ↔ det x = det y := by
  constructor
  · rintro ⟨γ⟩
    have hconst : Continuous (det ∘ γ) := det.continuous.comp γ.continuous
    simpa only [Function.comp_apply, γ.source, γ.target] using
      isPreconnected_univ.constant hconst.continuousOn (mem_univ 0) (mem_univ 1)
  · intro h
    obtain ⟨n, A, B, rfl, rfl⟩ :=
      SequentialColimitGroup.exists_of₂ (continuousOrthogonalBlockSucc ℝ) x y
    have hdet : (A : Matrix (Fin n) (Fin n) ℝ).det = (B : Matrix (Fin n) (Fin n) ℝ).det := by
      rw [← coe_det_of n A, ← coe_det_of n B, h]
    exact (TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq.2 hdet).map
      (SequentialColimitGroup.of (continuousOrthogonalBlockSucc ℝ) n).continuous

end StableOrthogonalGroup

end TauCeti
