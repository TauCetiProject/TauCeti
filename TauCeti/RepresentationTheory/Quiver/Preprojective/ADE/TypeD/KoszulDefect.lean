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

The outgoing-arrow annihilation theorem is supplied by
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.ForkTopPower`.
The grading and corner membership of the terminal word come from
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.TopDegree`.
Products use later-factor-first order.

As in the existing type-`D` word API, signless quotient carriers use
`forkNeighborSetFintype`; imported callers can select this local instance when
writing representatives. No restriction is placed on the characteristic.

## Main results

* `TauCeti.finrank_preprojectiveCorner_inf_iInf_ker_D_fork`: the graded left
  Koszul kernel at the fork is the line in degree `2n - 4` with source the fork.

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
  have he : E (σ (vertexIdempotent k (vertex DG f))) =
      π (vertexIdempotent k (Symmetrify.of.obj (OrientedQuiver.vertex DG o f))) :=
    C.signlessPreprojectiveAlgebraEquiv_vertexIdempotent k o f
  have hgrade : E t ∈ preprojectiveGrade k Q (2 * n - 4) :=
    C.signlessPreprojectiveAlgebraEquiv_mem_preprojectiveGrade k o
      (signlessPreprojectiveDForkTopWord_mem_grade k hn)
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
