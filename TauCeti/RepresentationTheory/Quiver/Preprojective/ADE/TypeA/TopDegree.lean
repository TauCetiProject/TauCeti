/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.Basis
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Corner
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.GraphGrading
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Resolution

/-!
# The top degree of the type-A preprojective algebra

The signless preprojective algebra of the path `Aₙ` is concentrated in path degrees below `n`.
This file proves that the bound is sharp: for every vertex `a`, the valley from `a` to the
opposite vertex `a.rev`, with bottom vertex `0`, is a nonzero element of degree `n - 1`.

These top valleys are killed on the left by every arrow. Consequently they give explicit nonzero
elements in degree `n - 1` of the kernels of the left maps in the vertex Koszul complexes. They
are the top-degree classes needed to identify the full type-`A` defect in the almost-Koszul
property of preprojective algebras.

Multiplication is in later-factor-first order. Thus the top valley begins at `a`, ends at `a.rev`,
and left multiplication appends an arrow at its terminal vertex.

## Main results

* `TauCeti.signlessPreprojectiveAValley_mem_signlessPreprojectiveCorner`: a valley lies in
  the graded corner whose degree is its path length.
* `TauCeti.signlessPreprojectiveGrade_A_eq_bot_of_le`: every degree at least `n` vanishes.
* `TauCeti.signlessPreprojectiveAValley_zero_ne_zero`: the opposite-vertex valley of length
  `n - 1` is nonzero.
* `TauCeti.signlessPreprojectiveATopValley` and
  `TauCeti.signlessPreprojectiveATopValley_mem_ker`: the top valley as a nonzero element of the
  left Koszul kernel.
* `TauCeti.not_injective_signlessPreprojectiveKoszulLeft_A`: the left Koszul map is not injective
  at any vertex of `Aₙ`.

## References

* S. Brenner, M. C. R. Butler and A. D. King, *Periodic algebras which are almost Koszul*,
  Algebr. Represent. Theory 5 (2002), Sections 3 and 4.
* C. M. Ringel, *The preprojective algebra of a quiver*, for the type-`A` normal forms and
  projective socles.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver MulOpposite

variable (k : Type*) {n : ℕ}

attribute [local instance] finiteNeighborSetFintype signlessPreprojectiveGradedAlgebra

local notation "AG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.A n))
local notation "Q" => DoubledQuiver AG
local notation "Π" => signlessPreprojectiveAlgebra k Q
local notation "σ" => signlessPreprojectiveMk k Q
local notation "e" => fun a : Fin (DynkinType.A n).rank =>
  σ (vertexIdempotent k (vertex AG a))

section CommRing

variable [CommRing k]

/-- A type-`A` valley belongs to the graded corner whose degree is the number of descents plus
climbs in its defining word. -/
theorem signlessPreprojectiveAValley_mem_signlessPreprojectiveCorner
    (a b : Fin (DynkinType.A n).rank) (m : ℕ) :
    signlessPreprojectiveAValley k a b m ∈
      signlessPreprojectiveCorner k Q ((a.val - m) + (b.val - m)) (vertex AG a) (vertex AG b) := by
  rw [mem_signlessPreprojectiveCorner_iff]
  refine ⟨?_, ?_⟩
  · rw [signlessPreprojectiveAValley_def]
    have hleft : e b ∈ signlessPreprojectiveGrade k Q 0 :=
      signlessPreprojectiveMk_mem_grade k Q (vertexIdempotent_mem_grade_zero _)
    have hright : e a ∈ signlessPreprojectiveGrade k Q 0 :=
      signlessPreprojectiveMk_mem_grade k Q (vertexIdempotent_mem_grade_zero _)
    simpa using mul_mem_signlessPreprojectiveGrade k Q
      (mul_mem_signlessPreprojectiveGrade k Q hleft
        (ladderValley_mem_grade k AG m (a.val - m) (b.val - m))) hright
  · have hid (i : Fin (DynkinType.A n).rank) : IsIdempotentElem (e i) :=
      IsIdempotentElem.map (vertexIdempotent_mul_self (k := k) (vertex AG i)) σ
    exact (mem_cornerSubmodule_iff k (hid b) (hid a)).1
      (signlessPreprojectiveAValley_mem_cornerSubmodule k a b m)

/-! ### The sharp top degree -/

/-- Every homogeneous piece of the signless preprojective algebra of `Aₙ` in degree at least
`n` vanishes. -/
theorem signlessPreprojectiveGrade_A_eq_bot_of_le (d : ℕ) (hd : n ≤ d) :
    signlessPreprojectiveGrade k Q d = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_signlessPreprojectiveGrade_iff k Q).1 hx
  rw [grade_eq_span_range] at hy
  refine Submodule.span_induction (p := fun y _ => σ y = 0) ?_ (map_zero σ) ?_ ?_ hy
  · intro z hz
    obtain ⟨⟨p, hp⟩, rfl⟩ := hz
    exact signlessPreprojectiveMk_A_ofPath_eq_zero_of_le k p (by omega)
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, add_zero]
  · intro c x _ hx
    rw [map_smul, hx, smul_zero]

/-- The bottom-zero valley from `a` to the opposite vertex has path length `n - 1`. -/
theorem signlessPreprojectiveAValley_zero_mem_top_corner
    (a : Fin (DynkinType.A n).rank) :
    signlessPreprojectiveAValley k a a.rev 0 ∈
      signlessPreprojectiveCorner k Q (n - 1) (vertex AG a) (vertex AG a.rev) := by
  have ha := a.isLt
  have hn := DynkinType.rank_A n
  have hsum : a.val + a.rev.val = n - 1 := by
    rw [Fin.val_rev]
    omega
  simpa only [Nat.sub_zero, hsum] using
    signlessPreprojectiveAValley_mem_signlessPreprojectiveCorner k a a.rev 0

end CommRing

section Field

variable [Field k]

/-- The bottom-zero valley from any vertex to its opposite vertex is nonzero. Hence the path
degree `n - 1` of the signless preprojective algebra of `Aₙ` is nontrivial. -/
@[simp]
theorem signlessPreprojectiveAValley_zero_ne_zero
    (a : Fin (DynkinType.A n).rank) :
    signlessPreprojectiveAValley k a a.rev 0 ≠ 0 := by
  let m : ↥(Finset.Icc (a.val + a.rev.val + 1 - n) (min a.val a.rev.val)) :=
    ⟨0, by
      have ha := a.isLt
      have hn := DynkinType.rank_A n
      simp only [Finset.mem_Icc, Fin.val_rev]
      omega⟩
  have h := (signlessPreprojectiveACornerBasis k a a.rev).ne_zero m
  intro hz
  apply h
  apply Subtype.ext
  rw [coe_signlessPreprojectiveACornerBasis_apply]
  exact hz

/-- The degree `n - 1` piece of the signless preprojective algebra of `Aₙ` is nonzero whenever
it has a vertex. Combined with `signlessPreprojectiveGrade_A_eq_bot_of_le`, this makes `n - 1`
the sharp top path degree. -/
theorem signlessPreprojectiveGrade_A_top_ne_bot
    (a : Fin (DynkinType.A n).rank) :
    signlessPreprojectiveGrade k Q (n - 1) ≠ ⊥ := by
  intro h
  have hmem := (mem_signlessPreprojectiveCorner_iff.1
    (signlessPreprojectiveAValley_zero_mem_top_corner k a)).1
  rw [h, Submodule.mem_bot] at hmem
  exact signlessPreprojectiveAValley_zero_ne_zero k a hmem

end Field

section CommRing

variable [CommRing k]

/-! ### The top-degree Koszul defect -/

/-- Every arrow leaving the terminal vertex kills the top valley. Its product with that valley
would have degree `n`, which vanishes. -/
@[simp]
theorem signlessPreprojectiveMk_ofArrow_mul_AValley_zero
    (a : Fin (DynkinType.A n).rank) {i : Q} (c : vertex AG a.rev ⟶ i) :
    σ (ofArrow c) * signlessPreprojectiveAValley k a a.rev 0 = 0 := by
  have hmem := signlessPreprojectiveMk_ofArrow_mul_mem_signlessPreprojectiveCorner c
    (signlessPreprojectiveAValley_zero_mem_top_corner k a)
  have hgrade := (mem_signlessPreprojectiveCorner_iff.1 hmem).1
  have hn : n ≤ (n - 1) + 1 := by
    have := a.isLt
    have hrank := DynkinType.rank_A n
    omega
  rw [signlessPreprojectiveGrade_A_eq_bot_of_le k ((n - 1) + 1) hn,
    Submodule.mem_bot] at hgrade
  exact hgrade

/-- The top valley from `a` to `a.rev`, regarded as an element of the right vertex projective at
`a.rev`. -/
noncomputable def signlessPreprojectiveATopValley
    (a : Fin (DynkinType.A n).rank) :
    signlessPreprojectiveRightProjective k (vertex AG a.rev) :=
  ⟨op (signlessPreprojectiveAValley k a a.rev 0),
    (mem_signlessPreprojectiveRightProjective_iff k _ _).2
      (signlessPreprojectiveMk_vertexIdempotent_mul_of_mem_signlessPreprojectiveCorner
        (signlessPreprojectiveAValley_zero_mem_top_corner k a))⟩

/-- The underlying algebra element of the top valley in the right vertex projective. -/
@[simp]
theorem unop_signlessPreprojectiveATopValley
    (a : Fin (DynkinType.A n).rank) :
    unop (signlessPreprojectiveATopValley k a : Πᵐᵒᵖ) =
      signlessPreprojectiveAValley k a a.rev 0 := (rfl)

/-- **The top valley lies in the left Koszul kernel**, in path degree `n - 1`. -/
theorem signlessPreprojectiveATopValley_mem_ker
    (a : Fin (DynkinType.A n).rank) :
    signlessPreprojectiveATopValley k a ∈
      LinearMap.ker (signlessPreprojectiveKoszulLeft k (vertex AG a.rev)) := by
  rw [LinearMap.mem_ker]
  ext i b
  apply unop_injective
  simpa only [unop_signlessPreprojectiveKoszulLeft_apply,
    unop_signlessPreprojectiveATopValley, Pi.zero_apply, Submodule.coe_zero, unop_zero] using
      signlessPreprojectiveMk_ofArrow_mul_AValley_zero k a (Quiver.reverse b)

end CommRing

section Field

variable [Field k]

/-- The top valley is nonzero in the right vertex projective. -/
@[simp]
theorem signlessPreprojectiveATopValley_ne_zero
    (a : Fin (DynkinType.A n).rank) :
    signlessPreprojectiveATopValley k a ≠ 0 := fun h =>
  signlessPreprojectiveAValley_zero_ne_zero k a
    (congrArg (fun z : signlessPreprojectiveRightProjective k (vertex AG a.rev) =>
      unop (z : Πᵐᵒᵖ)) h)

/-- **The left map in the type-`A` signless preprojective Koszul complex is not injective.** Its
kernel contains the nonzero top valley from `a` to `a.rev`, in degree `n - 1`. -/
theorem not_injective_signlessPreprojectiveKoszulLeft_A
    (a : Fin (DynkinType.A n).rank) :
    ¬ Function.Injective (signlessPreprojectiveKoszulLeft k (vertex AG a.rev)) := by
  intro hinj
  apply signlessPreprojectiveATopValley_ne_zero k a
  apply hinj
  rw [map_zero]
  exact LinearMap.mem_ker.mp (signlessPreprojectiveATopValley_mem_ker k a)

end Field

end TauCeti
