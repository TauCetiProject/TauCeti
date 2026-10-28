/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.TopDegree
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Koszul.Defect
import all TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basic

/-!
# The type-`D` Koszul defect at the fork

For `n ≥ 3`, the left Koszul kernel at the fork of `Dₙ` is the degree-`2n - 4`
line whose source is also the fork. The terminal alternating fork word is nonzero
over every field, including characteristic two, and every arrow leaving the fork
kills it. The general one-dimensionality theorem for finite-dimensional
preprojective algebras therefore determines the degree and source of this kernel.

The leaf relations kill the two outgoing leaf arrows. Along the long arm the
ladder relations kill the outgoing arrow followed by the `n - 3`-rd power of the
sum of the leaf backtracks. Alternation moves the remaining backtrack past that
power. Products use later-factor-first order.

As in the existing type-`D` word API, signless quotient carriers use
`forkNeighborSetFintype`; imported callers can select this local instance when
writing representatives. No restriction is placed on the characteristic.

## References

* S. Brenner, M. C. R. Butler and A. D. King, *Periodic algebras which are almost
  Koszul*, Algebr. Represent. Theory 5 (2002), Sections 3 and 4.
* W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the
  Deligne--Simpson problem*, Section 1, for the local relations.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

attribute [local instance] forkNeighborSetFintype

section CommRing

variable (k : Type*) [CommRing k] {n : ℕ}

local notation "DG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.D n))
local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver DG)
local notation "c" => n - 3
local notation "x" => signlessPreprojectiveDForkBacktrack (n := n) k true
local notation "y" => signlessPreprojectiveDForkBacktrack (n := n) k false

private theorem leafArrow_mul_topWord (hn : 3 ≤ n) (l : Bool) :
    signlessArrow k DG c (if l then c + 1 else c + 2) *
      signlessPreprojectiveDForkWords k hn (.inr ()) = 0 := by
  have hleaf : signlessArrow k DG c (if l then c + 1 else c + 2) *
      (if l then x else y) = 0 := by
    have h := signlessArrow_mul_signlessArrow_leaf k (G := DG)
      (by simpa only [DynkinType.rank_D] using diagramGraph_D_adj hn)
      (l := if l then c + 1 else c + 2) (by split_ifs <;> omega)
      (by rw [DynkinType.rank_D]; split_ifs <;> omega)
    cases l <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      signlessPreprojectiveDForkBacktrack_true,
      signlessPreprojectiveDForkBacktrack_false] at h ⊢ <;>
      rw [← mul_assoc, h, zero_mul]
  rw [signlessPreprojectiveDForkTopWord_eq]
  cases l
  · simp only [Bool.false_eq_true, ite_false] at hleaf ⊢
    have hsum : x * (x + y) ^ c + y * (x + y) ^ c = 0 := by
      simpa only [← add_mul, ← pow_succ'] using
        signlessPreprojectiveDForkBacktrack_add_pow_eq_zero k hn
    rw [eq_neg_of_add_eq_zero_left hsum, mul_neg, ← mul_assoc, hleaf, zero_mul, neg_zero]
  · simp only [ite_true] at hleaf ⊢
    rw [← mul_assoc, hleaf, zero_mul]

private theorem armArrow_mul_sum_pow (hn : 3 ≤ n) (hc : 0 < c) :
    signlessArrow k DG c (c - 1) * (x + y) ^ c = 0 := by
  let u := forkUp k DG c
  let d := forkDown k DG c
  have hrel (r : ℕ) : d (r + 1) * u (r + 1) + u r * d r = 0 :=
    forkDown_mul_forkUp_add k (G := DG) (by rw [DynkinType.rank_D]; omega)
      (by simpa only [DynkinType.rank_D] using diagramGraph_D_adj hn) r
  have hend : u c = 0 := by
    simp only [u, forkUp, Nat.sub_self, Nat.zero_sub]
    exact signlessArrow_fork_eq_zero k
      (by simpa only [DynkinType.rank_D] using diagramGraph_D_adj hn) (by omega)
  have hshift : (d 1 * u 1) ^ c = 0 := by
    have h := pow_d_mul_u_eq_zero (u := fun r => u (r + 1)) (d := fun r => d (r + 1))
      (fun r => hrel (r + 1)) (N := c - 1) (by simpa [Nat.sub_add_cancel hc] using hend)
    simpa only [zero_add, Nat.sub_add_cancel hc] using h
  have hu : u 0 * (d 0 * u 0) ^ c = 0 := by
    rw [← mul_pow_mul, eq_neg_of_add_eq_zero_right (hrel 0), neg_pow, hshift,
      mul_zero, zero_mul]
  have hsum : x + y = -(d 0 * u 0) := by
    simpa only [signlessPreprojectiveDForkBacktrack_true,
      signlessPreprojectiveDForkBacktrack_false, forkTurn, u, d] using
      eq_neg_of_add_eq_zero_right
        (forkDown_mul_forkUp_add_forkTurn k (G := DG) («c» := c)
          (by rw [DynkinType.rank_D]; omega)
          (by simpa only [DynkinType.rank_D] using diagramGraph_D_adj hn))
  have hzero : u 0 * (x + y) ^ c = 0 := by
    rw [hsum, neg_pow, ← mul_assoc, ((Commute.neg_one_right (u 0)).pow_right c).eq,
      mul_assoc, hu, mul_zero]
  simpa only [u, forkUp, Nat.sub_zero] using hzero

private theorem armArrow_mul_topWord (hn : 3 ≤ n) (hc : 0 < c) :
    signlessArrow k DG c (c - 1) * signlessPreprojectiveDForkWords k hn (.inr ()) = 0 := by
  have hx := signlessPreprojectiveDForkBacktrack_mul_self k hn true
  have hy := signlessPreprojectiveDForkBacktrack_mul_self k hn false
  have hxs : x * (x + y) = (x + y) * y := by
    simp only [mul_add, add_mul, hx, hy, zero_add, add_zero]
  have hcomm := commute_add_sq_of_mul_self_eq_zero hx hy
  rw [signlessPreprojectiveDForkTopWord_eq]
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' c
  · have hmove : x * (x + y) ^ c = (x + y) ^ c * x := by
      rw [hr, pow_mul]
      exact (hcomm.pow_right r).eq
    rw [hmove, ← mul_assoc, armArrow_mul_sum_pow k hn hc, zero_mul]
  · have hmove : x * (x + y) ^ c = (x + y) ^ c * y := by
      rw [hr, pow_succ, pow_mul, ← mul_assoc, (hcomm.pow_right r).eq,
        mul_assoc, hxs, ← mul_assoc]
    rw [hmove, ← mul_assoc, armArrow_mul_sum_pow k hn hc, zero_mul]

/-- Every arrow leaving the type-`D` fork kills its terminal alternating word. -/
theorem signlessPreprojectiveMk_ofArrow_mul_DForkTopWord_eq_zero (hn : 3 ≤ n)
    {w : DoubledQuiver DG} (b : vertex DG (preprojectiveDForkVertex n hn) ⟶ w) :
    signlessPreprojectiveMk k _ (ofArrow b) *
      signlessPreprojectiveDForkWords k hn (.inr ()) = 0 := by
  obtain ⟨j, rfl⟩ := exists_eq_vertex DG w
  rw [signlessPreprojectiveMk_ofArrow_eq_signlessArrow]
  simp only [vertexEquiv_symm_vertex, preprojectiveDForkVertex_val]
  have hj := (diagramGraph_D_adj hn _ j).1 ((nonempty_hom_iff DG).1 ⟨b⟩)
  simp only [preprojectiveDForkVertex_val] at hj
  rcases hj with h | h | h | h
  · omega
  · have h' : j.val = c - 1 := by omega
    simpa only [h'] using armArrow_mul_topWord k hn (by omega)
  · have hjn := j.isLt
    have hjn' : j.val < n := by simpa only [DynkinType.rank_D] using hjn
    obtain h' | h' : j.val = c + 1 ∨ j.val = c + 2 := by omega
    · simpa only [h', ite_true] using leafArrow_mul_topWord k hn true
    · simpa only [h', Bool.false_eq_true, ite_false] using leafArrow_mul_topWord k hn false
  · omega

end CommRing

section Field

variable (k : Type*) [Field k] {n : ℕ}

local notation "DG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.D n))
local notation "R" => DoubledQuiver DG
local notation "σ" => signlessPreprojectiveMk k R

attribute [local instance] Classical.propDecidable

private theorem exists_ne_zero_mem_preprojectiveCorner_D_fork (hn : 3 ≤ n)
    (o : Orientation DG) :
    ∃ z : preprojectiveAlgebra k (OrientedQuiver DG o),
      z ∈ preprojectiveCorner k (OrientedQuiver DG o) (2 * n - 4)
        (Symmetrify.of.obj (OrientedQuiver.vertex DG o (preprojectiveDForkVertex n hn)))
        (Symmetrify.of.obj (OrientedQuiver.vertex DG o (preprojectiveDForkVertex n hn))) ∧
      z ≠ 0 ∧ ∀ (w : Symmetrify (OrientedQuiver DG o))
        (b : w ⟶ Symmetrify.of.obj
          (OrientedQuiver.vertex DG o (preprojectiveDForkVertex n hn))),
        preprojectiveMk k _ (ofArrow (Quiver.reverse b)) * z = 0 := by
  let C := dColoring n
  let E := C.signlessPreprojectiveAlgebraEquiv k o
  let t := signlessPreprojectiveDForkWords k hn (.inr ())
  let f := preprojectiveDForkVertex n hn
  let Q := OrientedQuiver DG o
  let π := preprojectiveMk k Q
  have ht := signlessPreprojectiveDForkTopWord_mem_corner k hn
  have hfixed := (mem_signlessPreprojectiveCorner_iff.mp ht).2
  -- Keep the image vertex in the symmetrified carrier when simplifying its idempotent.
  have hobj : (unsymmetrifyMap DG o).obj (vertex DG f) =
      Symmetrify.of.obj (OrientedQuiver.vertex DG o f) := unsymmetrifyMap_obj DG o f
  have he : E (σ (vertexIdempotent k (vertex DG f))) =
      π (vertexIdempotent k (Symmetrify.of.obj (OrientedQuiver.vertex DG o f))) := by
    simp only [π, Q, E,
      SimpleGraph.Coloring.signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk,
      orientationPathAlgebraEquiv_apply, mapAlgHom_vertexIdempotent, hobj,
      rescale_vertexIdempotent]
  -- Both the orientation identification and arrow rescaling preserve path degree.
  have hgrade : E t ∈ preprojectiveGrade k Q (2 * n - 4) := by
    obtain ⟨p, hp, hpt⟩ := (mem_signlessPreprojectiveGrade_iff k R).1
      (signlessPreprojectiveDForkTopWord_mem_grade k hn)
    dsimp only [t]
    rw [← hpt]
    simp only [E, SimpleGraph.Coloring.signlessPreprojectiveAlgebraEquiv_signlessPreprojectiveMk]
    apply preprojectiveMk_mem_preprojectiveGrade
    apply rescale_mem_grade
    rw [orientationPathAlgebraEquiv_apply]
    rw [← gradeBy_const_one] at hp ⊢
    exact mapAlgHom_mem_gradeBy k _ _ (fun {_ _} _ => (1 : ℕ)) hp
  -- Arrows whose source is elsewhere vanish after the fork idempotent.
  have harrow {a b : R} (d : a ⟶ b) : σ (ofArrow d) * t = 0 := by
    by_cases ha : a = vertex DG f
    · subst a
      exact signlessPreprojectiveMk_ofArrow_mul_DForkTopWord_eq_zero k hn d
    · have hleft :=
        signlessPreprojectiveMk_vertexIdempotent_mul_of_mem_signlessPreprojectiveCorner ht
      dsimp only [t]
      rw [← hleft, ← mul_assoc, ← map_mul, ofArrow_eq_ofPath,
        ofPath_mul_vertexIdempotent_of_ne _ (Ne.symm ha), map_zero, zero_mul]
  refine ⟨E t, mem_preprojectiveCorner_iff.2 ⟨hgrade, ?_⟩, ?_, ?_⟩
  · rw [← he, ← map_mul, ← map_mul, hfixed]
  · exact fun hzero => signlessPreprojectiveDForkTopWord_ne_zero k hn
      (E.injective (hzero.trans (map_zero E).symm))
  · intro w b
    apply E.symm.injective
    rw [map_mul, E.symm_apply_apply, map_zero]
    simp only [E, SimpleGraph.Coloring.signlessPreprojectiveAlgebraEquiv_symm_preprojectiveMk,
      rescale_ofArrow, map_smul, orientationPathAlgebraEquiv_symm_apply,
      mapAlgHom_ofArrow, smul_mul_assoc, harrow, smul_zero]

/-- For every orientation of `Dₙ`, the graded left Koszul kernel at the fork is
one-dimensional in degree `2n - 4` with source the fork, and vanishes in every other
graded corner. -/
theorem finrank_preprojectiveCorner_inf_iInf_ker_D_fork (hn : 3 ≤ n)
    (o : Orientation DG) (m : ℕ) (i : OrientedQuiver DG o) :
    Module.finrank k ↥(preprojectiveCorner k (OrientedQuiver DG o) m
      (Symmetrify.of.obj i)
      (Symmetrify.of.obj (OrientedQuiver.vertex DG o (preprojectiveDForkVertex n hn))) ⊓
      ⨅ (w : Symmetrify (OrientedQuiver DG o))
        (b : w ⟶ Symmetrify.of.obj
          (OrientedQuiver.vertex DG o (preprojectiveDForkVertex n hn))),
        LinearMap.ker (LinearMap.mulLeft k (preprojectiveMk k _ (ofArrow (Quiver.reverse b))))) =
      if m = 2 * n - 4 ∧ i = OrientedQuiver.vertex DG o (preprojectiveDForkVertex n hn)
        then 1 else 0 := by
  classical
  obtain ⟨z, hz, hz0, hzb⟩ := exists_ne_zero_mem_preprojectiveCorner_D_fork k hn o
  exact finrank_preprojectiveCorner_inf_iInf_ker_eq_of_mem k hz hz0 hzb m i

end Field

end TauCeti
