/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.IteratedFunctionSystem.Basic
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.UniformSpace.Closeds

import TauCeti.Topology.MetricSpace.Closeds
import TauCeti.Topology.MetricSpace.HausdorffDistance

/-!
# The Hutchinson operator and Hutchinson's theorem

For an iterated function system `F : TauCeti.IFS ι X` with a finite nonempty index type, the
Hutchinson operator `F.hutchinson` sends a nonempty compact set `A` to `⋃ i, F i '' A`. It is
Lipschitz for the Hausdorff distance on `TopologicalSpace.NonemptyCompacts X`, with constant the
largest ratio `F.maxRatio` (`TauCeti.IFS.lipschitzWith_hutchinson`), so it is a contraction
(`TauCeti.IFS.contractingWith_hutchinson`). Its fixed points are exactly the attractors
(`TauCeti.IFS.isAttractor_iff_isFixedPt_hutchinson`).

Consequently, with no completeness assumption:

* two attractors of the same system are equal (`TauCeti.IFS.IsAttractor.unique`);
* the iterates of the operator approach an attractor geometrically,
  `d_H(Sⁿ A, K) ≤ rⁿ · d_H(A, K)` (`TauCeti.IFS.IsAttractor.hausdorffDist_hutchinson_iterate_le`);
* the collage estimate `d_H(A, K) ≤ d_H(A, S A) / (1 - r)` holds
  (`TauCeti.IFS.IsAttractor.hausdorffDist_le_hausdorffDist_hutchinson_div`), and with it
  `d_H(Sⁿ A, K) ≤ d_H(A, S A) · rⁿ / (1 - r)`
  (`TauCeti.IFS.IsAttractor.hausdorffDist_hutchinson_iterate_le_mul_div`);
* a nonempty bounded set `A` with `closure (⋃ i, F i '' A) = A` is the attractor
  (`TauCeti.IFS.IsAttractor.eq_of_closure_iUnion_image_eq`).

On a nonempty complete metric space the contraction mapping theorem, applied on the complete space
`NonemptyCompacts X`, produces the attractor `F.attractor`, and this is *Hutchinson's theorem*: a
finite nonempty iterated function system on a nonempty complete metric space has exactly one
attractor (`TauCeti.IFS.existsUnique_isAttractor`), to which the iterates of the Hutchinson
operator converge from every nonempty compact set (`TauCeti.IFS.tendsto_hutchinson_iterate`).

## References

* J. E. Hutchinson, *Fractals and self similarity*, Indiana Univ. Math. J. 30 (1981), 713–747,
  sections 3.1 and 3.2.
* C. J. Bishop and Y. Peres, *Fractals in Probability and Analysis*, Theorem 2.1.1.
-/

public section

open Filter Function Metric Set TopologicalSpace Topology
open scoped NNReal ENNReal

namespace TauCeti.IFS

variable {ι X : Type*} [MetricSpace X] (F : IFS ι X)

/-- The unions of the images of two sets under the maps of an iterated function system are at
Hausdorff extended distance at most the largest ratio times that of the two sets. -/
theorem hausdorffEDist_iUnion_image_le (A B : Set X) :
    hausdorffEDist (⋃ i, F i '' A) (⋃ i, F i '' B) ≤ F.maxRatio * hausdorffEDist A B := by
  refine hausdorffEDist_iUnion_le.trans (iSup_le fun i ↦ ?_)
  exact ((F.lipschitz i).hausdorffEDist_image_le (F.ratio_ne_zero i) A B).trans
    (mul_le_mul_left (ENNReal.coe_le_coe.2 (F.ratio_le_maxRatio i)) _)

/-! ### The Hutchinson operator -/

section Hutchinson

variable [Finite ι] [Nonempty ι]

/-- The Hutchinson operator of an iterated function system with a finite nonempty index type:
the map `A ↦ ⋃ i, F i '' A` on nonempty compact sets. -/
def hutchinson (A : NonemptyCompacts X) : NonemptyCompacts X where
  carrier := ⋃ i, F i '' A
  isCompact' := isCompact_iUnion fun i ↦ A.isCompact.image (F.continuous i)
  nonempty' := nonempty_iUnion.2 ⟨Classical.arbitrary ι, A.nonempty.image _⟩

@[simp, norm_cast]
theorem coe_hutchinson (A : NonemptyCompacts X) :
    (F.hutchinson A : Set X) = ⋃ i, F i '' A :=
  (rfl)

@[simp]
theorem mem_hutchinson {A : NonemptyCompacts X} {x : X} :
    x ∈ F.hutchinson A ↔ ∃ i, ∃ y ∈ A, F i y = x := by
  simp [← SetLike.mem_coe]

/-- The Hutchinson operator is Lipschitz for the Hausdorff distance, with constant the largest
ratio (Hutchinson 1981, 3.2(1)). -/
theorem lipschitzWith_hutchinson : LipschitzWith F.maxRatio F.hutchinson := fun A B ↦ by
  simp only [NonemptyCompacts.edist_eq, coe_hutchinson]
  exact F.hausdorffEDist_iUnion_image_le A B

/-- The Hutchinson operator is a contraction for the Hausdorff distance. -/
theorem contractingWith_hutchinson : ContractingWith F.maxRatio F.hutchinson :=
  ⟨F.maxRatio_lt_one, F.lipschitzWith_hutchinson⟩

variable {F}

/-- A nonempty compact set is an attractor exactly when it is a fixed point of the Hutchinson
operator. -/
theorem isAttractor_iff_isFixedPt_hutchinson {A : NonemptyCompacts X} :
    F.IsAttractor A ↔ IsFixedPt F.hutchinson A := by
  refine ⟨fun h ↦ NonemptyCompacts.ext (by simpa using h.iUnion_image_eq), fun h ↦ ?_⟩
  refine ⟨A.isCompact, A.nonempty, ?_⟩
  simpa using congrArg ((↑) : NonemptyCompacts X → Set X) h

end Hutchinson

/-! ### Attractors as fixed points -/

namespace IsAttractor

variable {F} {K : Set X}

/-- An attractor, as a nonempty compact set. -/
def toNonemptyCompacts (hK : F.IsAttractor K) : NonemptyCompacts X :=
  ⟨⟨K, hK.isCompact⟩, hK.nonempty⟩

@[simp]
theorem coe_toNonemptyCompacts (hK : F.IsAttractor K) : (hK.toNonemptyCompacts : Set X) = K :=
  (rfl)

theorem isFixedPt_hutchinson [Finite ι] [Nonempty ι] (hK : F.IsAttractor K) :
    IsFixedPt F.hutchinson hK.toNonemptyCompacts :=
  isAttractor_iff_isFixedPt_hutchinson.1 (by simpa using hK)

/-- Two attractors of the same iterated function system are equal. No completeness is needed: a
contraction has at most one fixed point. -/
theorem unique [Finite ι] {K' : Set X} (hK : F.IsAttractor K) (hK' : F.IsAttractor K') :
    K = K' := by
  have := hK.nonempty_index
  simpa using congrArg ((↑) : NonemptyCompacts X → Set X)
    (F.contractingWith_hutchinson.fixedPoint_unique' hK.isFixedPt_hutchinson
      hK'.isFixedPt_hutchinson)

variable [Finite ι] [Nonempty ι]

/-- *Rate of convergence.* The `n`-th iterate of the Hutchinson operator moves a nonempty compact
set `A` to within `F.maxRatio ^ n` times its Hausdorff distance to the attractor. -/
theorem hausdorffDist_hutchinson_iterate_le (hK : F.IsAttractor K) (A : NonemptyCompacts X)
    (n : ℕ) :
    hausdorffDist (F.hutchinson^[n] A : Set X) K ≤
      F.maxRatio ^ n * hausdorffDist (A : Set X) K := by
  have h := (F.lipschitzWith_hutchinson.iterate n).dist_le_mul A hK.toNonemptyCompacts
  rw [hK.isFixedPt_hutchinson.iterate n] at h
  simpa [TopologicalSpace.NonemptyCompacts.dist_eq] using h

/-- *Collage estimate.* The Hausdorff distance from a nonempty compact set `A` to the attractor is
at most `d_H(A, S A) / (1 - r)`, where `S` is the Hutchinson operator and `r` the largest ratio. -/
theorem hausdorffDist_le_hausdorffDist_hutchinson_div (hK : F.IsAttractor K)
    (A : NonemptyCompacts X) :
    hausdorffDist (A : Set X) K ≤
      hausdorffDist (A : Set X) (F.hutchinson A) / (1 - F.maxRatio) := by
  simpa [TopologicalSpace.NonemptyCompacts.dist_eq] using
    F.contractingWith_hutchinson.dist_le_of_fixedPoint A hK.isFixedPt_hutchinson

/-- The iterates of the Hutchinson operator approach the attractor geometrically, with the rate
controlled by the first step: `d_H(Sⁿ A, K) ≤ d_H(A, S A) · rⁿ / (1 - r)`. -/
theorem hausdorffDist_hutchinson_iterate_le_mul_div (hK : F.IsAttractor K)
    (A : NonemptyCompacts X) (n : ℕ) :
    hausdorffDist (F.hutchinson^[n] A : Set X) K ≤
      hausdorffDist (A : Set X) (F.hutchinson A) * F.maxRatio ^ n / (1 - F.maxRatio) := by
  refine (hK.hausdorffDist_hutchinson_iterate_le A n).trans ?_
  rw [mul_comm, mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right (hK.hausdorffDist_le_hausdorffDist_hutchinson_div A)
    (by positivity)

end IsAttractor

variable {F} in
/-- *Uniqueness among bounded sets.* If `K` is an attractor, every nonempty bounded set `A` with
`closure (⋃ i, F i '' A) = A` equals `K`: such an `A` is closed, and the Hausdorff distance between
`A` and `K` is finite and at most the largest ratio times itself. -/
theorem IsAttractor.eq_of_closure_iUnion_image_eq [Finite ι] {K A : Set X} (hK : F.IsAttractor K)
    (hne : A.Nonempty) (hb : Bornology.IsBounded A)
    (h : closure (⋃ i, F i '' A) = A) : A = K := by
  have hd : hausdorffEDist A K ≠ ∞ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded hne hK.nonempty hb hK.isCompact.isBounded
  have hle : hausdorffEDist A K ≤ F.maxRatio * hausdorffEDist A K :=
    calc hausdorffEDist A K
        = hausdorffEDist (closure (⋃ i, F i '' A)) (⋃ i, F i '' K) := by
          rw [h, hK.iUnion_image_eq]
      _ = hausdorffEDist (⋃ i, F i '' A) (⋃ i, F i '' K) := hausdorffEDist_closure_left
      _ ≤ F.maxRatio * hausdorffEDist A K := F.hausdorffEDist_iUnion_image_le A K
  have hA : IsClosed A := h ▸ isClosed_closure
  refine (hA.hausdorffEDist_zero_iff hK.isCompact.isClosed).1 ?_
  by_contra h0
  refine (ENNReal.mul_lt_of_lt_div ?_).not_ge hle
  rw [ENNReal.div_self h0 hd]
  exact_mod_cast F.maxRatio_lt_one

/-! ### Hutchinson's theorem -/

section Complete

variable [CompleteSpace X] [Nonempty X] [Finite ι] [Nonempty ι]

/-- The attractor of a finite nonempty iterated function system on a nonempty complete metric
space: the fixed point of the Hutchinson operator, given by the contraction mapping theorem on the
complete metric space of nonempty compact sets. -/
noncomputable def attractor : NonemptyCompacts X :=
  ContractingWith.fixedPoint F.hutchinson F.contractingWith_hutchinson

theorem isFixedPt_hutchinson_attractor : IsFixedPt F.hutchinson F.attractor :=
  ContractingWith.fixedPoint_isFixedPt _

theorem isAttractor_attractor : F.IsAttractor F.attractor :=
  isAttractor_iff_isFixedPt_hutchinson.2 F.isFixedPt_hutchinson_attractor

variable {F} in
theorem IsAttractor.eq_attractor {K : Set X} (hK : F.IsAttractor K) : K = F.attractor :=
  hK.unique F.isAttractor_attractor

theorem isAttractor_iff_eq_attractor {K : Set X} : F.IsAttractor K ↔ K = F.attractor :=
  ⟨IsAttractor.eq_attractor, fun h ↦ h ▸ F.isAttractor_attractor⟩

/-- **Hutchinson's theorem.** A finite nonempty iterated function system on a nonempty complete
metric space has exactly one attractor (Hutchinson 1981, 3.1(3)(i) with 3.2(1); Bishop and Peres,
Theorem 2.1.1(i)). -/
theorem existsUnique_isAttractor : ∃! K : Set X, F.IsAttractor K :=
  ⟨F.attractor, F.isAttractor_attractor, fun _ hK ↦ hK.eq_attractor⟩

/-- The iterates of the Hutchinson operator converge to the attractor from every nonempty compact
set, for the Hausdorff distance. -/
theorem tendsto_hutchinson_iterate (A : NonemptyCompacts X) :
    Tendsto (fun n ↦ F.hutchinson^[n] A) atTop (𝓝 F.attractor) :=
  ContractingWith.tendsto_iterate_fixedPoint _ A

end Complete

end TauCeti.IFS
