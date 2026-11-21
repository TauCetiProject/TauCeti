/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.BigCell.Triangular
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Blocks
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne

/-!
# Word factorization of the Weyl subgroup and the block-LDU test

For a Chevalley datum `D` over any commutative ring `A`, the pinned simple Weyl representatives
satisfy `nᵢ(1)² = hᵢ(-1) ∈ T_D(A)` and normalize the actual torus `T_D(A)`. Consequently every
element of `D.weylSubgroup A` decomposes as a positive word in the pinned simple Weyl
representatives followed by an actual torus point.

Over any nontrivial commutative ring `A`, combining this word decomposition with weight-space
block unitriangularity of `D.positivePoints A` and the Weyl-word block `LDU` criterion in
`Chevalley.BigCell.Triangular` forces any Weyl word equal to a torus point times a positive point
to evaluate to `1` in the Weyl group. Over fields, `D.weylProjection` evaluates such a product
to the Weyl-group element spelled by the word. The resulting intersection
`D.borelSubgroup A ⊓ D.weylSubgroup A = (D.torusPoints A).range` is established in
`Chevalley.Weyl.Intersection`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 22 and 27, and Chapter 5,
  Theorem 7.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.2 and 8.2.
-/

public section

open Multiplicative
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

section CommRing

variable (A : Type v) [CommRing A]

/-- Every product of pinned simple Weyl representatives belongs to `D.weylSubgroup A`. -/
theorem list_prod_map_weylElement_mem_weylSubgroup (l : List (Fin t.rank)) :
    (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod ∈ D.weylSubgroup A := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact D.weylElement_mem_weylSubgroup A i

/-- Every element of `D.weylSubgroup A` is a positive word in the pinned simple Weyl
representatives followed by a point of the actual torus, over every commutative ring. -/
theorem mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints {g : D.points A} :
    g ∈ D.weylSubgroup A ↔
      ∃ (l : List (Fin t.rank)) (s : Fin t.rank → Aˣ),
        (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod *
          D.torusPoints A s = g := by
  let r : Fin t.rank → D.points A := fun i => D.weylElement (t.simpleIndex ht i) A 1
  have htorus_mul (s₀ : Fin t.rank → Aˣ) (l : List (Fin t.rank)) (s : Fin t.rank → Aˣ) :
      ∃ s' : Fin t.rank → Aˣ,
        D.torusPoints A s₀ * ((l.map r).prod * D.torusPoints A s) =
          (l.map r).prod * D.torusPoints A s' := by
    have hnorm := D.weylSubgroup_le_normalizer_range_torusPoints A
      (inv_mem (D.list_prod_map_weylElement_mem_weylSubgroup A l))
    obtain ⟨s₁, hs₁⟩ := (Subgroup.mem_normalizer_iff.mp hnorm (D.torusPoints A s₀)).mp
      ⟨s₀, rfl⟩
    refine ⟨s₁ * s, ?_⟩
    have hcomm : D.torusPoints A s₀ * (l.map r).prod = (l.map r).prod * D.torusPoints A s₁ := by
      rw [hs₁]
      dsimp only [r]
      group
    rw [← mul_assoc, hcomm, mul_assoc, (D.torusPoints A).map_mul]
  constructor
  · intro hg
    rw [D.weylSubgroup_def] at hg
    induction hg using Subgroup.closure_induction_left with
    | one =>
      exact ⟨[], 1, by simp⟩
    | mul_left x hx y _ ih =>
      obtain ⟨l, s, rfl⟩ := ih
      rcases hx with ⟨s₀, rfl⟩ | ⟨i, rfl⟩
      · obtain ⟨s', hs'⟩ := htorus_mul s₀ l s
        exact ⟨l, s', hs'.symm⟩
      · exact ⟨i :: l, s, by simp [mul_assoc]⟩
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨l, s, rfl⟩ := ih
      rcases hx with ⟨s₀, rfl⟩ | ⟨i, rfl⟩
      · rw [← map_inv]
        obtain ⟨s', hs'⟩ := htorus_mul s₀⁻¹ l s
        exact ⟨l, s', hs'.symm⟩
      · have hri_inv : (r i)⁻¹ =
            r i * D.torusPoints A (D.simpleCorootParameter i A (-1))⁻¹ := by
          apply inv_eq_of_mul_eq_one_right
          rw [← mul_assoc, D.weylElement_mul_self i A, D.simpleCorootPoints_eq_torusPoints,
            ← (D.torusPoints A).map_mul, mul_inv_cancel, map_one]
        rw [hri_inv, mul_assoc]
        obtain ⟨s', hs'⟩ := htorus_mul (D.simpleCorootParameter i A (-1))⁻¹ l s
        refine ⟨i :: l, s', ?_⟩
        dsimp only [r] at hs' ⊢
        simp only [List.map_cons, List.prod_cons, mul_assoc]
        rw [← hs']
  · rintro ⟨l, s, rfl⟩
    exact mul_mem (D.list_prod_map_weylElement_mem_weylSubgroup A l)
      (D.torusPoints_mem_weylSubgroup A s)

/-- Over any nontrivial commutative ring, if a product of pinned simple Weyl representatives
equals an actual torus point times a positive point, then the Weyl word evaluates to `1` in the
Weyl group. -/
theorem geckWeylWordProd_eq_one_of_list_prod_eq_torusPoints_mul_positive [Nontrivial A]
    {l : List (Fin t.rank)} {s : Fin t.rank → Aˣ} {u : D.points A}
    (hu : u ∈ D.positivePoints A)
    (h : (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod =
      D.torusPoints A s * u) :
    t.geckWeylWordProd ht l = 1 := by
  rw [← D.exists_blockLDU_weylWord_iff l A (weightBlockEquiv (t.weightDegree ht) D.weight)]
  have hfun :
      (fun j => weightBlockEquiv (t.weightDegree ht) D.weight ⟨D.weight j, Set.mem_range_self j⟩) =
        orderedWeightBlock (t.weightDegree ht) D.weight := by
    funext j
    exact weightBlockEquiv_mk (t.weightDegree ht) D.weight j
  let Nmat : Matrix (Fin D.dim) (Fin D.dim) A :=
    ((D.torusPoints A s : Matrix.GeneralLinearGroup (Fin D.dim) A) :
      Matrix (Fin D.dim) (Fin D.dim) A)
  let Umat : Matrix (Fin D.dim) (Fin D.dim) A :=
    ((u : Matrix.GeneralLinearGroup (Fin D.dim) A) :
      Matrix (Fin D.dim) (Fin D.dim) A)
  have hNdiag : Nmat =
      Matrix.diagonal (fun j => (torusCharacter s (D.coordinateWeight j) : A)) := by
    simp only [Nmat, D.coe_torusPoints, kostantTorusMatrix_apply, diagGL_coe]
  refine ⟨1, Nmat, Umat, Matrix.blockUnitriangular_one, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hNdiag]
    exact Matrix.blockTriangular_diagonal _
  · rw [hNdiag]
    exact Matrix.blockTriangular_diagonal _
  · rw [hfun]
    exact D.blockUnitriangular_of_mem_positivePoints A hu
  · exact (Matrix.isUnit_iff_isUnit_det Nmat).mp
      (D.torusPoints A s : Matrix.GeneralLinearGroup (Fin D.dim) A).isUnit
  · rw [one_mul]
    simpa only [Nmat, Umat, Subgroup.coe_mul, Units.val_mul] using
      congrArg (fun x : D.points A =>
        ((x : Matrix.GeneralLinearGroup (Fin D.dim) A) :
          Matrix (Fin D.dim) (Fin D.dim) A)) h

/-- Conjugating any point of the actual weight-lattice torus by an element of `D.weylSubgroup A`
stays inside `D.borelSubgroup A`. -/
theorem weylSubgroup_conj_torusPoints_mem_borelSubgroup (w : D.weylSubgroup A)
    (s : Fin t.rank → Aˣ) :
    (w : D.points A) * D.torusPoints A s * (w : D.points A)⁻¹ ∈ D.borelSubgroup A :=
  D.range_torusPoints_le_borelSubgroup A <|
    (Subgroup.mem_normalizer_iff.mp
      (D.weylSubgroup_le_normalizer_range_torusPoints A w.property)
      (D.torusPoints A s)).mp ⟨s, rfl⟩

end CommRing

section Field

variable (K : Type v) [Field K]

/-- On a product of a Weyl word and an actual torus point, `D.weylProjection K` evaluates to the
Weyl-group element spelled by the word. -/
theorem weylProjection_list_prod_mul_torusPoints (l : List (Fin t.rank))
    (s : Fin t.rank → Kˣ) :
    D.weylProjection K
      ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod * D.torusPoints K s,
        mul_mem (D.list_prod_map_weylElement_mem_weylSubgroup K l)
          (D.torusPoints_mem_weylSubgroup K s)⟩ =
      t.geckWeylWordProd ht l := by
  have hword (m : List (Fin t.rank)) :
      D.weylProjection K ⟨(m.map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod,
        D.list_prod_map_weylElement_mem_weylSubgroup K m⟩ =
        t.geckWeylWordProd ht m := by
    induction m with
    | nil =>
      have hone :
          (⟨([].map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod,
            D.list_prod_map_weylElement_mem_weylSubgroup K []⟩ : D.weylSubgroup K) = 1 := by
        ext
        simp only [List.map_nil, List.prod_nil, Subgroup.coe_one]
      rw [hone, map_one, geckWeylWordProd_nil]
    | cons i m ih =>
      have hsplit : (⟨((i :: m).map fun j => D.weylElement (t.simpleIndex ht j) K 1).prod,
          D.list_prod_map_weylElement_mem_weylSubgroup K (i :: m)⟩ : D.weylSubgroup K) =
          ⟨D.weylElement (t.simpleIndex ht i) K 1, D.weylElement_mem_weylSubgroup K i⟩ *
            ⟨(m.map fun j => D.weylElement (t.simpleIndex ht j) K 1).prod,
              D.list_prod_map_weylElement_mem_weylSubgroup K m⟩ := by
        ext
        simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul]
      rw [hsplit, map_mul, D.weylProjection_weylElement K i, ih, geckWeylWordProd_cons]
  -- Split the `D.weylSubgroup K` subtype into the word product and torus factor by comparing
  -- their underlying elements in `D.points K`.
  have hmul : (⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod *
      D.torusPoints K s,
      mul_mem (D.list_prod_map_weylElement_mem_weylSubgroup K l)
        (D.torusPoints_mem_weylSubgroup K s)⟩ : D.weylSubgroup K) =
      ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod,
        D.list_prod_map_weylElement_mem_weylSubgroup K l⟩ *
        ⟨D.torusPoints K s, D.torusPoints_mem_weylSubgroup K s⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
  rw [hmul, map_mul, hword l, D.weylProjection_torusPoints K s, mul_one]

end Field

end TauCeti.DynkinType.ChevalleyDatum
